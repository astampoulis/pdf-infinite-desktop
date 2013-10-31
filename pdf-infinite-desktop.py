#!/usr/bin/python


# Infinite Desktop of PDFs
# written by Antonis Stampoulis
# published under the GPLv3
# 
# Needs GTK+ 3.0 and supporting libraries; only tested in Linux/Gnome 3.
# Needs gi-introspection for poppler; the following installs it on Ubuntu.
# sudo apt-get install gir1.2-poppler-0.18
#
# Put it into a directory with PDFs or execute it with
# python pdf-infinite-desktop.py (PDF directory)
# 
# Usage:
#  - Zoom in/out of the desktop with the mouse scroll wheel
#  - Select a PDF with the mouse, drag it around to move it
#  - Moving around the desktop either with arrow keys, or by
#     pressing spacing and then moving with the mouse
#     (pressing space again disables mouse move)
#  - Next/previous pages of a PDF with n/p or PgUp/PgDn
#  - Duplicate a PDF with d
#
#
# This was written sometime in 2009 as a proof-of-concept and was
# ported to current Clutter (1.16) in 2013. I have not yet adapted the
# code to use all the nice new features of Clutter, which would
# simplify a lot of the code.



from gi.repository import Clutter, Poppler, Gtk, Gdk, GLib, Cogl
import cairo
import os
import glob
import threading
import Queue
import pickle
import math
import weakref
import sys
from time import time
from collections import defaultdict
from collections import namedtuple

# TODO:
#  - make unused textures decay with time and if unused
#  - add borders around textures, and shadows
#  - add labels and textboxes..
#  - quadtree
#  - schedule_load should have two cases for delay: one small when a large
#      percentage of visible textures are of bad factor, and one large for
#      other cases
#  - weakref / timeout / manage memory
#  - better indication for new / selected 
#  - animations

DEFAULT_SCALE = 0.1
SCALE_LOAD_TIMEOUT = 500
MAX_TEXTURES_KEEP = 5
MIN_LOAD_SCALE = 0.1
MAX_LOAD_SCALE = 2.5
PAN_SPEED = 50.0
PAN_THRESHOLD = 0.2
PAN_KEEP_INTERVAL = 30
FREEING_STRATEGY = None # can be "aggressive"
FULLSCREEN = False
DIMENSIONS = (1280,800)

TextureInfo = namedtuple('TextureInfo', ['origscale', 'doc', 'pagenum'])
CloneInfo = namedtuple('CloneInfo', ['origscale', 'doc', 'pagenum', 'time'])


def idle_add_once(func, *args):

    def wrapperfunc():
        func(*args)
        return False

    GLib.idle_add(wrapperfunc)

class TextureManager(threading.Thread):

    def __init__(self, desktop):
        threading.Thread.__init__(self)
        self.requestslock = threading.Lock()
        self.requests = []
        self.requestsSets = []
        self.tasks = threading.Semaphore(0)
        self.tasks.up = self.tasks.release
        self.tasks.down = self.tasks.acquire
        self.enable = threading.Semaphore(0)
        self.enable.up = self.enable.release
        self.enable.down = self.enable.acquire

        self.desktop = desktop
        self.cache = defaultdict(lambda:defaultdict(lambda:[]))
        self.cacheUse = dict()
        self.cachelock = threading.Lock()
        self.cachetime = 0

        self.daemon = True

    def request_load_textures(self, requests, replaceable = False):
        self.requestslock.acquire()
        islastrep = len(self.requests) > 0 and self.requests[-1][0]
        if islastrep and not replaceable:
            self.requests.insert(-1, (replaceable, requests))
            self.requestsSets.insert(-1, set(requests))
        else:
            self.requests.append( (replaceable, requests) )
            self.requestsSets.append( set(requests) )
        self.tasks.up()
        self.requestslock.release()

    def run(self):
        
        while True:

            self.tasks.down()
            self.requestslock.acquire()
            (replaceable, requests) = self.requests.pop(0)
            self.requestsSets.pop(0)
            self.requestslock.release()

            for request in requests:

                self.enable.down()
                
                if replaceable:
                    self.requestslock.acquire()
                    shouldbreak = len(self.requests) > 0 and request not in self.requestsSets[0] #!= requests and request
                    self.requestslock.release()
                    if shouldbreak:
                        idle_add_once(self.enable.up)
                        break

                self.cachelock.acquire()
                isnecessary = request not in self.cacheUse
                self.cachelock.release()

                if isnecessary:
                    self.load_texture(*request)
                    idle_add_once(self.desktop.update)
                
                idle_add_once(self.enable.up)

    def load_texture(self, doc, pagenum, scale):

        page = doc.get_page(pagenum)

        w, h = page.get_size()
        w *= scale
        h *= scale

        w = int(w)
        h = int(h)
        surface = cairo.ImageSurface(cairo.FORMAT_RGB24, w, h)
        context = cairo.Context(surface)

        context.set_source_rgb(1,1,1)
        context.rectangle(0,0,w,h)
        context.fill()
        context.scale(scale,scale)
        page.render(context)

        texture = Gdk.pixbuf_get_from_surface(context.get_target(), 0, 0, w, h)
        textureinfo = TextureInfo(origscale = scale, doc = doc, pagenum = pagenum)

        self.cachelock.acquire()
        if len(self.cache[doc][pagenum]) >= MAX_TEXTURES_KEEP:
            _, txtr, txtrinfo = self.cache[doc][pagenum].pop(0)
            del self.cacheUse[doc, pagenum, txtrinfo.origscale]
            del txtr

        self.cacheUse[doc, pagenum, scale] = 0
        insindex = len(self.cache[doc][pagenum])
        for i, (s, _, _) in enumerate(self.cache[doc][pagenum]):
            if scale >= s:
                insindex = i
                break
        self.cache[doc][pagenum].insert( insindex, (scale, texture, textureinfo) )
        self.cachetime = time()
        
        self.cachelock.release()
            
    def get_texture(self, doc, pagenum, reqscale):

        texture = None
        textureinfo = None
        
        self.cachelock.acquire()
        c = self.cache[doc][pagenum]
        if len(c) > 0:
            previous = c[0]
            for cur in c:
                curscale, _, _ = cur
                if curscale < reqscale: break
                previous = cur
            _, texture, textureinfo = previous
        readtime = time()
        self.cachelock.release()

        if texture: 
            image = Clutter.Image()
            image.set_data(texture.get_pixels(),
                           Cogl.PixelFormat.RGBA_8888 if texture.get_has_alpha() else Cogl.PixelFormat.RGB_888,
                           texture.get_width(),
                           texture.get_height(),
                           texture.get_rowstride())
            actor = Clutter.Actor()
            actor.set_content(image)
            actor.set_size(texture.get_width(), texture.get_height())

            cloneinfo = CloneInfo(textureinfo.origscale, doc, pagenum, readtime)
            if FREEING_STRATEGY == "aggressive":
                self.cachelock.acquire()
                self.cacheUse[doc, pagenum, textureinfo.origscale] += 1
                self.cachelock.release()
            return (actor, cloneinfo)
        else:
            return None

    def release_texture(self, texture, textureinfo):

        doc = textureinfo.doc
        pagenum = textureinfo.pagenum
        scale = textureinfo.origscale
        del texture

        if FREEING_STRATEGY == "aggressive":
            self.cachelock.acquire()
            self.cacheUse[doc, pagenum, scale] -= 1
            if self.cacheUse[doc, pagenum, scale] == 0:
                for i, (s, txtr, _) in enumerate(self.cache[doc][pagenum]):
                    if s == scale:
                        delindex = i
                        break
                _, txtr, _ = self.cache[doc][pagenum].pop(delindex)
                del txtr
                del self.cacheUse[doc, pagenum, scale]
            self.cachelock.release()
        

    def available_texture(self, doc, pagenum):
        self.cachelock.acquire()
        isthere = len(self.cache[doc][pagenum]) > 0
        self.cachelock.release()
        return isthere

    def is_uptodate_texture(self, time):
        self.cachelock.acquire()
        isit = time > self.cachetime
        self.cachelock.release()
        return isit

class Camera:

    def __init__(self, stage, scale, x = 0.0, y = 0.0):
        self.scale = scale
        self.x = x
        self.y = y
        self.vwidth, self.vheight = stage.get_size()

    def set_view_size(self, vwidth, vheight):
        self.vwidth, self.vheight = vwidth, vheight

    def get_bounds(self):
        return (self.x, self.y,
                self.x + self.vwidth/self.scale,
                self.y + self.vheight/self.scale)

    def translate_to_view(self, x, y):
        return ((x - self.x) * self.scale), ((y - self.y) * self.scale)

    def translate_from_view(self, x, y):
        return x / self.scale  + self.x, y / self.scale + self.y

    def in_bounds(self, x, y, w, h):
        startx, starty = self.translate_to_view(x,y)
        endx, endy = self.translate_to_view(x+w, y+h)
        return startx < self.vwidth and endx > 0 and starty < self.vheight and endy > 0

    def get_size(self):
        return (self.vwidth/self.scale, self.vheight/self.scale)

    def handle_zoom(self, direction, x, y):
        oldscale = self.scale
        if direction == Clutter.ScrollDirection.UP and self.scale < MAX_LOAD_SCALE:
            self.scale += self.scale / 20.0
        elif direction == Clutter.ScrollDirection.DOWN:
            self.scale -= self.scale / 20.0
        if abs(oldscale - self.scale) > 0.000001:
            self.x += (1.0 / oldscale - 1.0 / self.scale) * float(x)
            self.y += (1.0 / oldscale - 1.0 / self.scale) * float(y)

    def handle_center_on_radial(self, pos):
        mx, my = pos
        cx, cy = float(self.vwidth) / 2.0, float(self.vheight) / 2.0
        percent = math.hypot(float(mx) - cx, float(my) - my) / math.hypot(cx, cy)

        if mx < cx: sx = -1.0
        else: sx = 1.0

        if my < cy: sy = -1.0
        else: sy = 1.0
        
        self.x += sx * percent * PAN_SPEED / self.scale
        self.y += sy * percent * PAN_SPEED / self.scale
        return percent > PAN_THRESHOLD

    def handle_move_by(self, sx, sy):
        self.x += sx * PAN_SPEED / self.scale
        self.y += sy * PAN_SPEED / self.scale
        
    def handle_center_on(self, mx, my):
        
        cx, cy = float(self.vwidth) / 2.0, float(self.vheight) / 2.0
        px, py = 2.0 * (mx / float(self.vwidth) - 0.5), 2.0 * (my / float(self.vheight) - 0.5)
        self.x += px * PAN_SPEED / self.scale
        self.y += py * PAN_SPEED / self.scale
        return abs(px) > PAN_THRESHOLD or abs(py) > PAN_THRESHOLD

    def handle_zoom_box(self, (sx,sy,ex,ey)):

        w = float(ex - sx)
        h = float(ey - sy)

        mx = sx + w/2.0
        my = sy + h/2.0
        self.scale = min( self.vwidth / w, self.vheight / h)
        self.x = mx - self.vwidth / (2.0 * self.scale)
        self.y = my - self.vheight / (2.0 * self.scale)
        

class PdfEntity:

    def __init__(self, desktop, doc, pagenum):

        self.pagenum = pagenum
        self.desktop = desktop
        self.doc = doc
        self.pagenum = pagenum
        self.page = doc.get_page(pagenum)
        self.texture = None
        self.textureinfo = None
        self.texturescale = 0
        self.texturepage = 0
        self.texturetime = 0

    def page_change(self, add):

        newpage = self.pagenum + add
        if newpage < 0 or newpage >= self.doc.get_n_pages(): return False
        self.pagenum = newpage
        self.page = self.doc.get_page(newpage)
        return True

    def get_title(self):
        fn = self.doc.filename.split("/")[-1]
        fn = fn.split(".")[0]
        fields = fn.split("_")
        fn = fields[0] + " : " + " ".join(fields[1:])
        return fn
        
    def update(self):

        w, h = self.page.get_size()
        x, y = self.desktop.space.get_pos(self)
        
        camera = self.desktop.camera
        texturemgr = self.desktop.texturemgr
        texture = None
        textureinfo = None
        canvas = None

        if camera.in_bounds(x,y,w,h):
            if self.texture == None or (not texturemgr.is_uptodate_texture(self.texturetime)) or self.texturescale != camera.scale or self.texturepage != self.pagenum:
                result = texturemgr.get_texture(self.doc, self.pagenum, camera.scale)
            else:
                result = self.texture, self.textureinfo
            if result:
                texture, textureinfo = result
                factor = float(camera.scale) / textureinfo.origscale
                texture.set_scale(factor, factor)
                texture.set_position(*camera.translate_to_view(x,y))
                texture.entity = self
                self.texturetime = textureinfo.time
                self.texturescale = textureinfo.origscale

        if texture != self.texture:
            if self.texture:
                self.texture.hide()
                self.desktop.stage.remove_actor(self.texture)
                texturemgr.release_texture(self.texture, self.textureinfo)
            self.texture = texture
            self.textureinfo = textureinfo

            if texture:
                self.desktop.stage.add_actor(texture)
                texture.show()

    def is_visible(self):
        w, h = self.page.get_size()
        x, y = self.desktop.space.get_pos(self)
        return self.desktop.camera.in_bounds(x,y,w,h)

    def get_bounds(self):
        x, y = self.desktop.space.get_pos(self)
        w, h = self.page.get_size()
        return (x, y, x + w, y + h)

    def get_size(self):
        return self.page.get_size()

    def get_cameradist_metric(self):
        x,y = self.desktop.space.get_pos(self)
        w,h = self.get_size()
        mx, my = x+w/2.0, y+h/2.0
        cx,cy,cw,ch = self.desktop.camera.get_bounds()
        cmx, cmy = cx+cw/2.0, cy+ch/2.0
        return math.hypot(cmx-mx, cmy-my)

    def delete(self):
        if self.texture:
            self.texture.hide()
            self.desktop.stage.remove_actor(self.texture)
            self.desktop.texturemgr.release_texture(self.texture)

class Desktop:

    def __init__(self, directory):

        self.space = None
        self.active_entity = None
        self.selected_entity = None
        self.timeout = None
        self.pantimeout = None
        self.do_scroll = False
        self.lastMouseX = 0
        self.lastMouseY = 0
        self.label = None
        self.show_tooltip = True
        self.directory = directory

        # set up texture cache
        self.texturemgr = TextureManager(self)
        
        # set up stage

        stage = Clutter.Stage()
        stage.set_size(*DIMENSIONS)
        try:
            background = Clutter.Texture.new_from_file(os.path.join(directory, "background.jpg"))
            self.background = background
            self.background.show()
            stage.add_actor(self.background)
        except Exception:
            c = Clutter.Color.get_static(Clutter.StaticColor.DARK_BLUE)
            stage.set_color(c)
            self.background = None

        stage.connect('scroll-event', self.on_zoom_event)
        stage.connect('button-press-event', self.on_mouse_press_event)
        stage.connect('button-release-event', self.on_mouse_release_event)
        stage.connect('motion-event', self.on_motion_event)
        stage.connect('key-press-event', self.on_key_press_event)
        stage.connect('fullscreen', self.on_resize)
        stage.connect('unfullscreen', self.on_resize)
        stage.connect('delete-event', self.on_quit)

        self.stage = stage
        self.stage.show_all()

        g = glob.glob(os.path.join(directory, "*.pdf"))

        try:
            f = open(os.path.join(directory, ".pdf-desktop-config"), "r")
            camerascale, camerax, cameray, config = pickle.load(f)
            f.close()
            existing = set(list(g))
            config = filter(lambda (fn, pg, pos, size) : fn in existing, config)
            fns = set([fn for (fn, _, _, _) in config ])
            for fn in existing - fns:
                config.append( (fn,0,None,None) )
        except IOError:
            camerascale = DEFAULT_SCALE
            camerax = 0.0
            cameray = 0.0
            config = [ (fn, 0, None, None) for fn in g ]

        # set up camera
        camera = Camera(stage, camerascale, camerax, cameray)
        self.camera = camera

        # set up docs
        fns = set([fn for (fn,_,_,_) in config])
        docs = dict([(fn, Poppler.Document.new_from_file("file://" + fn, None)) for fn in fns])
        for (fn, doc) in docs.items(): doc.filename = fn

        # set up space
        space = Space(self)
        for (fn, pg, pos, _) in config:
            entity = PdfEntity(self, docs[fn], pg)
            space.add(entity, pos)
        self.space = space

        # init requests
        entities = self.space.get_entities_sorted()
        requests = defaultdict(lambda:[])

        for entity, (pos, size) in entities:

            scales = requests[entity.doc, entity.pagenum]
            if self.camera.in_bounds(pos[0], pos[1], size[0], size[1]) and not self.camera.scale in scales and self.camera.scale >= MIN_LOAD_SCALE:
                requests[entity.doc, entity.pagenum].insert(0, self.camera.scale)
            if not DEFAULT_SCALE in scales:
                requests[entity.doc, entity.pagenum].append( DEFAULT_SCALE )

        requestlist = []
        added = set()
        for entity, _ in entities:
            if (entity.doc, entity.pagenum) in added: continue
            for scale in requests[entity.doc, entity.pagenum]:
                requestlist.append( (entity.doc, entity.pagenum, scale) )
            added.add( (entity.doc, entity.pagenum) )

        self.texturemgr.request_load_textures(requestlist)

        self.update()

        if FULLSCREEN: self.stage.set_fullscreen(True)

    def stretch_background(self):
        if self.background:
            w,h = self.background.get_base_size()
            sw,sh = self.stage.get_size()
            self.background.set_scale(sw/float(w), sh/float(h))

    def update(self):
        if self.space:
            self.space.update()
            self.stage.show_all()

    def updated_view(self, cancel_timeouts = True):
        if self.timeout and cancel_timeouts:
            GLib.source_remove(self.timeout)
        self.timeout = GLib.timeout_add(SCALE_LOAD_TIMEOUT, self.schedule_load_textures_for_scale)
        

    def schedule_load_textures_for_scale(self):

        if self.camera.scale >= MIN_LOAD_SCALE: scale = self.camera.scale
        else: scale = DEFAULT_SCALE
        visible = self.space.get_visible_entities()
        reqs = [ (ent.doc, ent.pagenum, scale) for ent in visible ]
        self.texturemgr.request_load_textures(reqs, replaceable = True)
        return False

    def on_zoom_event(self, stage, event):
        self.camera.handle_zoom(event.direction, event.x, event.y)
        self.update()
        self.updated_view()
        return True

    def on_mouse_press_event(self, stage, event):
        if event.button == 1:
            actor = stage.get_actor_at_pos(Clutter.PickMode.ALL, event.x, event.y)
            try:
                self.active_entity = actor.entity
                self.selected_entity = self.active_entity
                wx, wy = self.camera.translate_from_view(event.x, event.y)
                sx, sy = self.space.get_pos(self.active_entity)                
                self.dispx, self.dispy = wx - sx, wy - sy
                self.update()
            except Exception:
                pass

    def on_mouse_release_event(self, stage, event):
        self.active_entity = None

    def pan_camera(self, x, y, doupdate = False):
        
        if self.camera.handle_center_on(x,y):
            self.updated_view(cancel_timeouts = False)
            if doupdate: self.update()
            return True
        else:
            return False

    def move_camera(self, x, y):
        self.camera.handle_move_by(x,y)
        self.updated_view(cancel_timeouts = False)
        self.update()

    def on_motion_event(self, stage, event):

        self.lastMouseX = event.x
        self.lastMouseY = event.y

        update = False

        if self.do_scroll:        
            if self.pantimeout:
                GLib.source_remove(self.pantimeout)
                self.pantimeout = None
            if self.pan_camera(event.x, event.y):
                self.pantimeout = GLib.timeout_add(PAN_KEEP_INTERVAL, self.pan_camera, event.x, event.y, True)
            update = True
            
        if self.active_entity:  # event.modifier_state == Clutter.BUTTON1_MASK and 
            entity = self.active_entity
            wx, wy = self.camera.translate_from_view(event.x, event.y)
            self.space.set_pos(entity, (wx - self.dispx, wy - self.dispy))
            update = True

        if update: self.update()

        if self.show_tooltip:
            try:
                actor = stage.get_actor_at_pos(event.x, event.y)
                ent = actor.entity
                title = ent.get_title()
                if self.label:
                    self.stage.remove_actor(self.label)
                    self.label = None
                self.label = Clutter.Text()
                self.label.set_text(title)
                self.label.set_color(Clutter.color_parse("white"))
                self.label.set_position(0,0)
                self.label.show()
                self.stage.add_actor(self.label)
                self.stage.show_all()
            except Exception:
                if self.label:
                    self.stage.remove_actor(self.label)
                    self.label = None


    def on_key_press_event(self, stage, event):

        if event.keyval == Clutter.KEY_Escape:
            self.on_quit()

        if event.keyval == Clutter.KEY_space:
            self.do_scroll = not self.do_scroll
            if not self.do_scroll and self.pantimeout:
                GLib.source_remove(self.pantimeout)
                self.pantimeout = None

        if event.keyval == Clutter.KEY_Home:
            self.camera.handle_zoom_box(self.space.get_bounds())
            self.update()
            self.updated_view()

        if event.keyval == Clutter.KEY_Down: self.move_camera(0, +1)
        elif event.keyval == Clutter.KEY_Up: self.move_camera(0, -1)
        elif event.keyval == Clutter.KEY_Left: self.move_camera(-1, 0)
        elif event.keyval == Clutter.KEY_Right: self.move_camera(+1, 0)

        if event.keyval == Clutter.KEY_question:
            self.show_tooltip = not self.show_tooltip

        # doesn't work for some reason -- stage.get_size is b0rked
        if event.keyval == Clutter.KEY_f:
            self.toggle_fullscreen()

        entities = self.space.get_visible_entities()
        if len(entities) == 1: self.selected_entity = entities[0]
        elif len(entities) == 0: self.selected_entity = None
        if not self.selected_entity: return

        pagechanged = False
        if event.keyval in [Clutter.KEY_n, Clutter.KEY_Page_Down]:
            pagechanged = self.selected_entity.page_change(+1)
        if event.keyval in [Clutter.KEY_p, Clutter.KEY_Page_Up]:
            pagechanged = self.selected_entity.page_change(-1)

        if pagechanged:
            if self.texturemgr.available_texture(self.selected_entity.doc, self.selected_entity.pagenum):
                self.update()
            self.schedule_load_textures_for_scale()
    
        if event.keyval == Clutter.KEY_d:
            oldent = self.selected_entity
            entity = PdfEntity(self, oldent.doc, oldent.pagenum)
            x, y = self.camera.translate_from_view(self.lastMouseX, self.lastMouseY)
            self.space.add(entity, (x,y))
            self.selected_entity = entity
            self.active_entity = entity
            self.dispx = 0
            self.dispy = 0
            self.update()

        if event.keyval == Clutter.KEY_Delete:
            if self.space.remove_entity(self.selected_entity):
                self.selected_entity = None
                self.active_entity = None
                self.update()

        if event.keyval == Clutter.KEY_End:
            self.camera.handle_zoom_box(self.selected_entity.get_bounds())
            self.update()
            self.updated_view()

    def on_quit(self, *args):
        self.save_config()
        Clutter.main_quit()
        
        exit(0)

    def save_config(self):
        config = self.space.get_config()
        f = open(os.path.join(self.directory, ".pdf-desktop-config"), "w")
        pickle.dump( (self.camera.scale, self.camera.x, self.camera.y, config), f)
        f.close()

    def toggle_fullscreen(self):
        if self.stage.get_fullscreen():
            self.stage.set_fullscreen(False)
        else:
            self.stage.set_fullscreen(True)

    def on_resize(self,stage):
        self.camera.set_view_size(*self.stage.get_size())
        self.stretch_background()
        self.update()

    def run(self):
        self.stage.show_all()
        idle_add_once(self.texturemgr.start)
        idle_add_once(self.texturemgr.enable.up)
        Clutter.main()
        
class Space:

    def __init__(self, desktop):
        self.desktop = desktop
        self.entities_dict = {}

    def update(self):
        # render selected entity last
        for key in self.entities_dict:
            if key != self.desktop.selected_entity:
                key.update()
        if self.desktop.selected_entity:
            selected = self.desktop.selected_entity
            selected.update()
            
    def add(self, entity, pos = None):

        w, h = entity.get_size()
        if pos == None:
            xs, ys = [], []
            for npos, nsize in self.entities_dict.values():
                if npos != None and nsize != None:
                    nx,ny = npos
                    nw,nh = nsize
                    xs.append(nx+nw)
                    ys.append(ny+nh)
            if xs != []:
                x, y = max(xs)+10.0, 10.0
            else:
                x, y = 10.0, 10.0
            self.entities_dict[entity] = ((x,y), (w,h))
        else:
            self.entities_dict[entity] = (pos, (w,h))

    def get_pos(self, entity):
        return self.entities_dict[entity][0]

    def set_pos(self, entity, newpos):
        pos, size = self.entities_dict[entity]
        self.entities_dict[entity] = newpos, size

    def get_bounds(self):
        startx = [ x for (x,y), (w,h) in self.entities_dict.values() ]
        starty = [ y for (x,y), (w,h) in self.entities_dict.values() ]
        endx = [ x+w for (x,y), (w,h) in self.entities_dict.values() ]
        endy = [ y+h for (x,y), (w,h) in self.entities_dict.values() ]
        return (min(startx), min(starty), max(endx), max(endy))

    def get_visible_entities(self):
        return [ ent for ent in self.entities_dict.keys() if ent.is_visible() ]

    def get_entities_sorted(self):
        s = self.entities_dict.items()
        s.sort(key = lambda (entity, (pos, size)) : entity.get_cameradist_metric())
        return s

    def get_config(self):
        config = [ (entity.doc.filename, entity.pagenum, pos, size) for entity, (pos, size) in self.entities_dict.items() ]
        return config

    def remove_entity(self, ent):

        times = 0
        for entity in self.entities_dict.keys():
            if entity.doc == ent.doc: times += 1
            
        if times > 1:
            ent.delete()
            del self.entities_dict[ent]
            return True
        
        return False

if __name__ == "__main__":
    
    GLib.threads_init()
    Clutter.threads_init()
    Clutter.init(sys.argv)

    Clutter.threads_enter()
    directory = os.getcwd()
    if len(sys.argv) > 1:
        directory = sys.argv[1]
    desktop = Desktop(directory)
    desktop.run()
    Clutter.threads_leave()


