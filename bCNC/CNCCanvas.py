# $Id: CNCCanvas.py,v 1.7 2014/10/15 15:04:06 bnv Exp $
#
# Author:       vvlachoudis@gmail.com
# Date: 24-Aug-2014

import math
import time
import sys
from tkinter_gl import GLCanvas

import OpenGL
if sys.platform == 'linux':
    # PyOpenGL is broken with wayland:
    OpenGL.setPlatform('x11')

from OpenGL.GL import *
from ctypes import c_void_p
from pyglm.glm import mat4x4, ortho, identity, value_ptr, inverse, translate, rotate, vec2, vec3, vec4, inverse, normalize, lookAt
import os

from tkinter import (
    TclError,
    FALSE,
    N,
    S,
    W,
    E,
    NS,
    EW,
    NSEW,
    CENTER,
    NONE,
    BOTH,
    LEFT,
    RIGHT,
    RAISED,
    HORIZONTAL,
    VERTICAL,
    ALL,
    DISABLED,
    LAST,
    SCROLL,
    UNITS,
    StringVar,
    IntVar,
    BooleanVar,
    Button,
    Canvas,
    Checkbutton,
    Frame,
    Label,
    Radiobutton,
    Scrollbar,
    OptionMenu,
)
import tkinter

import bmath
import Camera
import tkExtra
import Utils
from CNC import CNC

# Probe mapping we need PIL and numpy
try:
    from PIL import Image, ImageTk
    import numpy

    # Resampling image based on PIL library and converting to RGB.
    # options possible: NEAREST, BILINEAR, BICUBIC, ANTIALIAS
    RESAMPLE = Image.NEAREST  # resize type
except Exception:
    from tkinter import Image
    numpy = None
    RESAMPLE = None

try:
    import OpenGL
    if sys.platform == 'linux':
        # PyOpenGL is broken with wayland:
        OpenGL.setPlatform('x11')
    from OpenGL import GL
except ImportError:
    raise ImportError(
        """
        This example requires PyOpenGL.

        You can install it with "pip install PyOpenGL".
        """)

ANTIALIAS_CHEAP = False

VIEW_XY = 0
VIEW_XZ = 1
VIEW_YZ = 2
VIEW_ISO1 = 3
VIEW_ISO2 = 4
VIEW_ISO3 = 5
VIEWS = ["X-Y", "X-Z", "Y-Z", "ISO1", "ISO2", "ISO3"]

INSERT_WIDTH2 = 3
GANTRY_R = 4
GANTRY_X = GANTRY_R * 2  # 10
GANTRY_Y = GANTRY_R  # 5
GANTRY_H = GANTRY_R * 5  # 20
DRAW_TIME = 5  # Maximum draw time permitted

INSERT_COLOR = "Blue"
GANTRY_COLOR = "Red"
MARGIN_COLOR = "Magenta"
GRID_COLOR = "Gray"
BOX_SELECT = "Cyan"
TAB_COLOR = "DarkOrange"
TABS_COLOR = "Orange"
WORK_COLOR = "Orange"
CAMERA_COLOR = "Cyan"
CANVAS_COLOR = "White"

ENABLE_COLOR = "Black"
DISABLE_COLOR = "LightGray"
SELECT_COLOR = "Blue"
SELECT2_COLOR = "DarkCyan"
PROCESS_COLOR = "Green"

BLUE = 255.
DARK_CYAN = 35723.
ORANGE = 16753920.
DARK_ORANGE = 16747520.
LIGHT_GRAY = 13882323.
BLACK = 0.

MOVE_COLOR = "DarkCyan"
RULER_COLOR = "Green"
PROBE_TEXT_COLOR = "Green"

INFO_COLOR = "Gold"

SELECTION_TAGS = ("sel", "sel2", "sel3", "sel4")

ACTION_SELECT = 0
ACTION_SELECT_SINGLE = 1
ACTION_SELECT_AREA = 2
ACTION_SELECT_DOUBLE = 3

ACTION_PAN = 10
ACTION_ORIGIN = 11

ACTION_MOVE = 20
ACTION_ROTATE = 21
ACTION_GANTRY = 22
ACTION_WPOS = 23

ACTION_RULER = 30
ACTION_ADDORIENT = 31

SHIFT_MASK = 1
CONTROL_MASK = 4
ALT_MASK = 8
CONTROLSHIFT_MASK = SHIFT_MASK | CONTROL_MASK
CLOSE_DISTANCE = 5
MAXDIST = 10000
ZOOM = 1.25

S60 = math.sin(math.radians(60))
C60 = math.cos(math.radians(60))

DEF_CURSOR = ""
MOUSE_CURSOR = {
    ACTION_SELECT: DEF_CURSOR,
    ACTION_SELECT_AREA: "right_ptr",
    ACTION_PAN: "fleur",
    ACTION_ORIGIN: "cross",
    ACTION_MOVE: "hand1",
    ACTION_ROTATE: "exchange",
    ACTION_GANTRY: "target",
    ACTION_WPOS: "diamond_cross",
    ACTION_RULER: "tcross",
    ACTION_ADDORIENT: "tcross",
}

# Path lines Flags are stored in a float32 value for each vertex. 
# Each flag is represented by a bit in that value. It can store up to 24 tags (24 representative bits in an integer float32)
FLAG_SELECTED = 0b1
FLAG_ENABLED = 0b10
#FLAG_XXX = 0b100
#FLAG_XXX = 0b1000

openglFolder = f"{os.path.abspath(os.path.dirname(__file__))}{os.sep}opengl{os.sep}"

# -----------------------------------------------------------------------------
def mouseCursor(action):
    return MOUSE_CURSOR.get(action, DEF_CURSOR)


# =============================================================================
# Raise an alarm exception
# =============================================================================
class AlarmException(Exception):
    pass


# =============================================================================
# Drawing canvas
# =============================================================================
class CNCCanvas(GLCanvas):
    def __init__(self, master, app, *kw, **kwargs):
        super().__init__(master) # TODO: Handle takefocus and background parameters

        profile = 'legacy' # Opengl 2.1

        # Global variables
        self.view = 0
        self.app = app
        self.cnc = app.cnc
        self.gcode = app.gcode
        self.actionVar = IntVar()

        # Canvas binding
        self.bind("<Configure>", self.configureEvent)
        self.bind("<Motion>", self.motion)
        self.bind("<Button-1>", self.click)
        self.bind("<B1-Motion>", self.buttonMotion)
        self.bind("<ButtonRelease-1>", self.release)
        self.bind("<Double-1>", self.double)

        self.bind("<Button-2>", self.midClick)
        self.bind("<B2-Motion>", self.pan)
        self.bind("<ButtonRelease-2>", self.panRelease)
        self.bind("<Button-4>", self.mouseZoomIn)
        self.bind("<Button-5>", self.mouseZoomOut)
        self.bind("<MouseWheel>", self.wheel)
        self.bind("<Button-3>", self.rightClick)
        self.bind("<B3-Motion>", self.rotate)

        self.bind("<Shift-Button-4>", self.panLeft)
        self.bind("<Shift-Button-5>", self.panRight)
        self.bind("<Control-Button-4>", self.panUp)
        self.bind("<Control-Button-5>", self.panDown)

        self.bind("<Control-Key-Left>", self.panLeft)
        self.bind("<Control-Key-Right>", self.panRight)
        self.bind("<Control-Key-Up>", self.panUp)
        self.bind("<Control-Key-Down>", self.panDown)

        self.bind("<Escape>", self.actionCancel)
        self.bind("<Key>", self.handleKey)

        self.bind("<Control-Key-S>", self.cameraSave)
        self.bind("<Control-Key-t>", self.__test)

        self.bind("<Control-Key-equal>", self.menuZoomIn)
        self.bind("<Control-Key-minus>", self.menuZoomOut)

        self.x0 = 0.0
        self.y0 = 0.0
        self.zoom = 1.
        self.__tzoom = 1.0  # delayed zoom (temporary)
        self._items = {}
        self._viewCenterX = 0
        self._viewCenterY = 0

        self._x = self._y = 0
        self._xp = self._yp = 0
        self.action = ACTION_SELECT
        self._mouseAction = None
        self._inDraw = False  # semaphore for parsing
        self._gantry1 = None
        self._gantry2 = None
        self._margin = None
        self._amargin = None
        self._workarea = None
        self._vector = None
        self._lastActive = None
        self._lastGantry = None
        self._gantryRadius = None
        self._gantryLocation = vec3(0, 0, 0)
        self._drawRequested = False

        self._probeImage = None
        self._probeTkImage = None
        self._probe = None

        self.camera = Camera.Camera("aligncam")
        self.cameraAnchor = CENTER  # Camera anchor location "" for gantry
        self.cameraRotation = 0.0  # camera Z angle
        self.cameraXCenter = 0.0  # camera X center offset
        self.cameraYCenter = 0.0  # camera Y center offset
        self.cameraScale = 10.0  # camera pixels/unit
        self.cameraEdge = False  # edge detection
        self.cameraR = 1.5875  # circle radius in units (mm/inched)
        self.cameraDx = 0  # camera shift vs gantry
        self.cameraDy = 0
        self.cameraZ = None  # if None it will not make any Z movement for the camera
        self.cameraSwitch = False  # Look at spindle(False) or camera(True)
        self._cameraAfter = None  # Camera anchor location "" for gantry
        self._cameraMaxWidth = 640  # on zoom over this size crop the image
        self._cameraMaxHeight = 480
        self._cameraImage = None
        self._cameraHori = None  # cross hair items
        self._cameraVert = None
        self._cameraCircle = None
        self._cameraCircle2 = None

        self.draw_axes = True  # Drawing flags
        self.draw_grid = True
        self.draw_margin = True
        self.draw_probe = True
        self.draw_workarea = True
        self.draw_paths = True
        self.draw_rapid = True  # draw rapid motions
        self._wx = self._wy = self._wz = 0.0  # work position
        self._dx = self._dy = self._dz = 0.0  # work-machine position

        self._vx0 = self._vy0 = self._vz0 = 0  # vector move coordinates
        self._vx1 = self._vy1 = self._vz1 = 0  # vector move coordinates

        self._orientSelected = None

        # OPENGL vars
        self.MVMatrix = identity(mat4x4) # Model View Matrix
        self.PMatrix = ortho(-100, 100, -100, 100, -10000, 10000) # Projection matrix. Updated on resize
        
        # self.lines: Dictionary of lines to be drawn. 
        # key: line_id (We increment it for each new line)
        self._line_id = 1
        # item: [x1, y1, z1, x2, y2, z2, dashRatio, selected]
        # dashRatio: 0-1. 1 is solid line
        # Selected: 1 or 0
        self.lines = {}
        self.pathLines = numpy.array([], dtype=numpy.float32)
        self._modelCenter = vec3(0, 0, 0)
        self._modelSize = 100.0
        # Background gradiend colors
        self.bgColorUp = vec3(0.175, 0.215, 0.392)
        self.bgColorDn = vec3(0.4, 0.4, 0.6)
        # Axes
        self.axesVertices = numpy.array([], dtype=numpy.float32)
        # Gantry
        self.gantryVertices = numpy.array([], dtype=numpy.float32)
        # Grid
        self.gridVertices = numpy.array([], dtype=numpy.float32)
        # Margins
        self.marginVertices = numpy.array([], dtype=numpy.float32)
        # Work Area
        self.workAreaVertices = numpy.array([], dtype=numpy.float32)
        # Selection Rectangle
        self.SelectionRectVertices = numpy.array([], dtype=numpy.float32)
        
        self.reset()
        self.initGL()
        self.createAxes()

        self.initPosition()
        

    def initGL(self):
        # ----- BACKGROUND PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "BackgroundVS.shd", "r") as file:
            BackgroundVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "BackgroundFS.shd", "r") as file:
            BackgroundFSCode = file.read()

        self.backgroundProgram = self.createProgram(BackgroundVSCode, BackgroundFSCode)

        # Create a Vertex Buffer Object (VBO)
        self.backgroundVBO = glGenBuffers(1)
        
        # Since the background is fixed, we set the buffer data here
        glUseProgram(self.backgroundProgram)      
        glBindBuffer(GL_ARRAY_BUFFER, self.backgroundVBO)
        
        vertices = numpy.array([
            1, 1, 0, self.bgColorUp.x, self.bgColorUp.y, self.bgColorUp.z,
            -1, 1, 0, self.bgColorUp.x, self.bgColorUp.y, self.bgColorUp.z,
            -1, -1, 0, self.bgColorDn.x, self.bgColorDn.y, self.bgColorDn.z,
            1, 1, 0, self.bgColorUp.x, self.bgColorUp.y, self.bgColorUp.z,
            -1, -1, 0, self.bgColorDn.x, self.bgColorDn.y, self.bgColorDn.z,
            1, -1, 0, self.bgColorDn.x, self.bgColorDn.y, self.bgColorDn.z
        ], dtype=numpy.float32)
        
        glBufferData(GL_ARRAY_BUFFER, vertices.nbytes, vertices, GL_STATIC_DRAW)
        
        glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        # ----- PATH PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "PathVS.shd", "r") as file:
            PathVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "PathFS.shd", "r") as file:
            PathFSCode = file.read()

        self.shader_program = self.createProgram(PathVSCode, PathFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.pathVBO = glGenBuffers(1)
        
        # ----- AXES PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "AxesVS.shd", "r") as file:
            AxesVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "AxesFS.shd", "r") as file:
            AxesFSCode = file.read()

        self.axesProgram = self.createProgram(AxesVSCode, AxesFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.axesVBO = glGenBuffers(1)
        
        # ----- GANTRY PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "GantryVS.shd", "r") as file:
            GantryVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "GantryFS.shd", "r") as file:
            GantryFSCode = file.read()

        self.gantryProgram = self.createProgram(GantryVSCode, GantryFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.gantryVBO = glGenBuffers(1)
        
        # ----- GRID PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "GridVS.shd", "r") as file:
            GridVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "GridFS.shd", "r") as file:
            GridFSCode = file.read()

        self.gridProgram = self.createProgram(GridVSCode, GridFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.gridVBO = glGenBuffers(1)
        
        # ----- LINES PROGRAM ------
        # Generic program for solid colored lines
        # Vertex Shader code
        with open(openglFolder + "LinesVS.shd", "r") as file:
            LinesVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "LinesFS.shd", "r") as file:
            LinesFSCode = file.read()

        self.linesProgram = self.createProgram(LinesVSCode, LinesFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.marginsVBO = glGenBuffers(1)
        self.workAreaVBO = glGenBuffers(1)

        # ----- SELECTION RECT PROGRAM ------
        # Program to draw the selection rectangle
        # Vertex Shader code
        with open(openglFolder + "SelectionRectVS.shd", "r") as file:
            SelectionRectVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "SelectionRectFS.shd", "r") as file:
            SelectionRectFSCode = file.read()

        self.SelectionRectProgram = self.createProgram(SelectionRectVSCode, SelectionRectFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.SelectionRectVBO = glGenBuffers(1)


        
        glClearColor(1.0, 1.0, 1.0, 1.0)
        
    def createProgram(self, vertexShaderCode, fragmentShaderCode):
        # Compile Vertex Shader
        vertex_shader = glCreateShader(GL_VERTEX_SHADER)
        glShaderSource(vertex_shader, vertexShaderCode)
        glCompileShader(vertex_shader)
        if not glGetShaderiv(vertex_shader, GL_COMPILE_STATUS):
            raise RuntimeError(glGetShaderInfoLog(vertex_shader))

        # Compile Fragment Shader
        fragment_shader = glCreateShader(GL_FRAGMENT_SHADER)
        glShaderSource(fragment_shader, fragmentShaderCode)
        glCompileShader(fragment_shader)
        if not glGetShaderiv(fragment_shader, GL_COMPILE_STATUS):
            raise RuntimeError(glGetShaderInfoLog(fragment_shader))

        # Link Shaders into a Program
        shader_program = glCreateProgram()
        glAttachShader(shader_program, vertex_shader)
        glAttachShader(shader_program, fragment_shader)
        glLinkProgram(shader_program)
        if not glGetProgramiv(shader_program, GL_LINK_STATUS):
            raise RuntimeError(glGetProgramInfoLog(shader_program))

        # Clean up shaders (no longer needed after linking)
        glDeleteShader(vertex_shader)
        glDeleteShader(fragment_shader)
        
        return shader_program
        
    def create_line(self, xyz, colorRGB, dashRatio, flags):
        # xyz is an array of arrays of 3d coords
        self.lines[self._line_id] = [xyz, colorRGB, dashRatio, flags]
        
        id = self._line_id
        # Increment the line id for the next line
        self._line_id += 1
        
        return id
    
    def update_buffer(self, buffer, vertexData):        
        # In order to be compatible with Pi 3, we are using GLSL 1.0. It doesn't allow constant parameters per line in the fragment shader. They are always
        # interpolated between vertices. Then, we must assign the parameter twice, once per vertex, with the same value
        vertexArray = []
        
        maxX = maxY = maxZ = -999999
        minX = minY = minZ = 999999
        
        for id, data in vertexData.items():
            xyz = data[0]
            # We take xyz coords in pairs to create separate lines
            for i in range(len(xyz) - 1):
                
                length = math.sqrt(math.pow(xyz[i+1][0]-xyz[i][0], 2) + math.pow(xyz[i+1][1]-xyz[i][1], 2) + math.pow(xyz[i+1][2]-xyz[i][2], 2))
                colorValue = (data[1][0] << 16) + (data[1][1] << 8) + data[1][2] # RGB
                
                vertexArray.extend([
                    # Vertex 1
                    id,
                    xyz[i][0], # x1
                    xyz[i][1], # y1
                    xyz[i][2], # z1
                    0, # 0 for starting point, length for end point
                    colorValue, # RGB
                    data[2], # dashRatio
                    data[3], # flags
                    # Vertex 2
                    id,
                    xyz[i+1][0], # x1
                    xyz[i+1][1], # y1
                    xyz[i+1][2], # z1
                    length,
                    colorValue, # RGB
                    data[2], # dashRatio
                    data[3], # flags
                ])
                
                # TODO: Optimize this
                maxX = max(max(maxX, xyz[i][0]), xyz[i+1][0])
                maxY = max(max(maxY, xyz[i][1]), xyz[i+1][1])
                maxZ = max(max(maxZ, xyz[i][2]), xyz[i+1][2])
                minX = min(min(minX, xyz[i][0]), xyz[i+1][0])
                minY = min(min(minY, xyz[i][1]), xyz[i+1][1])
                minZ = min(min(minZ, xyz[i][2]), xyz[i+1][2])

        if len(vertexData) == 0:
            self._modelCenter = vec3(0, 0, 0)
            self._modelSize = 100
        else:
            self._modelCenter = vec3((maxX + minX) / 2, (maxY + minY) / 2, (maxZ + minZ) / 2)
            self._modelSize = math.sqrt(math.pow(maxX-minX, 2) + math.pow(maxY-minY, 2) + math.pow(maxZ-minZ, 2))
        
        self.pathLines = numpy.array(vertexArray, dtype=numpy.float32)
        
        #glUseProgram(self.shader_program) 
        glBindBuffer(GL_ARRAY_BUFFER, buffer)
        glBufferData(GL_ARRAY_BUFFER, self.pathLines.nbytes, self.pathLines, GL_DYNAMIC_DRAW)

        glBindBuffer(GL_ARRAY_BUFFER, 0)  # Unbind the VBO
    
    # Calculate arguments for antialiasing
    def antialias_args(self, args, winc=0.5, cw=2):
        nargs = {}

        # set defaults
        nargs["width"] = 1
        nargs["fill"] = "#000"

        # get original args
        for arg in args:
            nargs[arg] = args[arg]
        if nargs["width"] == 0:
            nargs["width"] = 1

        # calculate width
        nargs["width"] += winc

        # calculate color
        cbg = self.winfo_rgb(self.cget("bg"))
        cfg = list(self.winfo_rgb(nargs["fill"]))
        cfg[0] = (cfg[0] + cbg[0] * cw) / (cw + 1)
        cfg[1] = (cfg[1] + cbg[1] * cw) / (cw + 1)
        cfg[2] = (cfg[2] + cbg[2] * cw) / (cw + 1)
        nargs["fill"] = "#{:02x}{:02x}{:02x}".format(
            int(cfg[0] / 256), int(cfg[1] / 256), int(cfg[2] / 256)
        )

        return nargs

    # Override alias method if antialiasing enabled:
    """ if ANTIALIAS_CHEAP:

        def create_line(self, *args, **kwargs):
            nkwargs = self.antialias_args(kwargs)
            super().create_line(*args, **nkwargs)
            return super().create_line(*args, **kwargs) """

    # ----------------------------------------------------------------------
    def reset(self):
        self.zoom = 1.0

    # ----------------------------------------------------------------------
    # Set status message
    # ----------------------------------------------------------------------
    def status(self, msg):
        self.event_generate("<<Status>>", data=msg)

    # ----------------------------------------------------------------------
    def setMouseStatus(self, event):
        data = "%.4f %.4f %.4f" % self.canvas2xyz(
            event.x, event.y
        )
        self.event_generate("<<Coords>>", data=data)

    # ----------------------------------------------------------------------
    # Update scrollbars
    # ----------------------------------------------------------------------
    def _updateScrollBars(self):
        """Update scroll region for new size"""
        bb = self.bbox("all")
        if bb is None:
            return
        x1, y1, x2, y2 = bb
        dx = x2 - x1
        dy = y2 - y1
        # make it 3 times bigger in each dimension
        # so when we zoom in/out we don't touch the borders
        self.configure(scrollregion=(x1 - dx, y1 - dy, x2 + dx, y2 + dy))

    # ----------------------------------------------------------------------
    def handleKey(self, event):
        if event.char == "a":
            self.event_generate("<<SelectAll>>")
        elif event.char == "A":
            self.event_generate("<<SelectNone>>")
        elif event.char == "e":
            self.event_generate("<<Expand>>")
        elif event.char == "f":
            self.fit2Screen()
        elif event.char == "g":
            self.setActionGantry()
        elif event.char == "l":
            self.event_generate("<<EnableToggle>>")
        elif event.char == "m":
            self.setActionMove()
        elif event.char == "n":
            self.event_generate("<<ShowInfo>>")
        elif event.char == "o":
            self.setActionOrigin()
        elif event.char == "r":
            self.setActionRuler()
        elif event.char == "s":
            self.setActionSelect()
        elif event.char == "x":
            self.setActionPan()
        elif event.char == "z":
            self.menuZoomIn()
        elif event.char == "Z":
            self.menuZoomOut()

    # ----------------------------------------------------------------------
    def setAction(self, action):
        self.action = action
        self.actionVar.set(action)
        self._mouseAction = None
        self.config(cursor=mouseCursor(self.action), background="White")

    # ----------------------------------------------------------------------
    def actionCancel(self, event=None):
        if self.action != ACTION_SELECT or (
            self._mouseAction != ACTION_SELECT and self._mouseAction is not None
        ):
            self.setAction(ACTION_SELECT)
            return "break"

    # ----------------------------------------------------------------------
    def setActionSelect(self, event=None):
        self.setAction(ACTION_SELECT)
        self.status(_("Select objects with mouse"))

    # ----------------------------------------------------------------------
    def setActionPan(self, event=None):
        self.setAction(ACTION_PAN)
        self.status(_("Pan viewport"))

    # ----------------------------------------------------------------------
    def setActionOrigin(self, event=None):
        self.setAction(ACTION_ORIGIN)
        self.status(_("Click to set the origin (zero)"))

    # ----------------------------------------------------------------------
    def setActionMove(self, event=None):
        self.setAction(ACTION_MOVE)
        self.status(_("Move graphically objects"))

    # ----------------------------------------------------------------------
    def setActionGantry(self, event=None):
        self.setAction(ACTION_GANTRY)
        self.config(background="seashell")
        self.status(_("Move CNC gantry to mouse location"))

    # ----------------------------------------------------------------------
    def setActionWPOS(self, event=None):
        self.setAction(ACTION_WPOS)
        self.config(background="ivory")
        self.status(
            _("Set mouse location as current machine position (X/Y only)"))

    # ----------------------------------------------------------------------
    def setActionRuler(self, event=None):
        self.setAction(ACTION_RULER)
        self.status(_("Drag a ruler to measure distances"))

    # ----------------------------------------------------------------------
    def setActionAddMarker(self, event=None):
        self.setAction(ACTION_ADDORIENT)
        self.status(_("Add an orientation marker"))

    # ----------------------------------------------------------------------
    # Convert canvas cx,cy coordinates to machine space
    # ----------------------------------------------------------------------
    def canvas2Machine(self, cx, cy):
        u = cx / self.zoom
        v = cy / self.zoom

        if self.view == VIEW_XY:
            return u, -v, None

        elif self.view == VIEW_XZ:
            return u, None, -v

        elif self.view == VIEW_YZ:
            return None, u, -v

        elif self.view == VIEW_ISO1:
            return 0.5 * (u / S60 + v / C60), 0.5 * (u / S60 - v / C60), None

        elif self.view == VIEW_ISO2:
            return 0.5 * (u / S60 - v / C60), -0.5 * (u / S60 + v / C60), None

        elif self.view == VIEW_ISO3:
            return -0.5 * (u / S60 + v / C60), -0.5 * (u / S60 - v / C60), None

    # ----------------------------------------------------------------------
    # Image (pixel) coordinates to machine
    # ----------------------------------------------------------------------
    def image2Machine(self, x, y):
        return self.canvas2Machine(self.canvasx(x), self.canvasy(y))

    # ----------------------------------------------------------------------
    # Move gantry to mouse location
    # ----------------------------------------------------------------------
    def actionGantry(self, x, y):
        u, v, w = self.image2Machine(x, y)
        self.app.goto(u, v, w)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Set the work coordinates to mouse location
    # ----------------------------------------------------------------------
    def actionWPOS(self, x, y):
        u, v, w = self.image2Machine(x, y)
        self.app.mcontrol._wcsSet(u, v, w)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Add an orientation marker at mouse location
    # ----------------------------------------------------------------------
    def actionAddOrient(self, x, y):
        cx, cy = self.snapPoint(self.canvasx(x), self.canvasy(y))
        u, v, w = self.canvas2Machine(cx, cy)
        if u is None or v is None:
            self.status(
                _("ERROR: Cannot set X-Y marker  with the current view"))
            return
        self._orientSelected = len(self.gcode.orient)
        self.gcode.orient.add(CNC.vars["wx"], CNC.vars["wy"], u, v)
        self.event_generate("<<OrientSelect>>", data=self._orientSelected)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Find item selected
    # ----------------------------------------------------------------------
    def click(self, event):
        self.focus_set()
        self._x = self._xp = event.x
        self._y = self._yp = event.y

        if event.state & CONTROLSHIFT_MASK == CONTROLSHIFT_MASK:
            self.actionGantry(event.x, event.y)
            return

        elif self.action == ACTION_SELECT:
            self._mouseAction = ACTION_SELECT_SINGLE

        elif self.action in (ACTION_MOVE, ACTION_RULER):
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            if self.action == ACTION_RULER and self._vector is not None:
                # Check if we hit the existing ruler
                coords = self.coords(self._vector)
                if abs(coords[0] - i) <= CLOSE_DISTANCE and abs(
                    coords[1] - j <= CLOSE_DISTANCE
                ):
                    # swap coordinates
                    coords[0], coords[2] = coords[2], coords[0]
                    coords[1], coords[3] = coords[3], coords[1]
                    self.coords(self._vector, *coords)
                    self._vx0, self._vy0, self._vz0 = self.canvas2xyz(
                        coords[0], coords[1]
                    )
                    self._mouseAction = self.action
                    return
                elif abs(coords[2] - i) <= CLOSE_DISTANCE and abs(
                    coords[3] - j <= CLOSE_DISTANCE
                ):
                    self._mouseAction = self.action
                    return

            if self._vector:
                self.delete(self._vector)
            if self.action == ACTION_MOVE:
                # Check if we clicked on a selected item
                try:
                    for item in self.find_overlapping(
                        i - CLOSE_DISTANCE,
                        j - CLOSE_DISTANCE,
                        i + CLOSE_DISTANCE,
                        j + CLOSE_DISTANCE,
                    ):
                        tags = self.gettags(item)
                        if (
                            "sel" in tags
                            or "sel2" in tags
                            or "sel3" in tags
                            or "sel4" in tags
                        ):
                            break
                    else:
                        self._mouseAction = ACTION_SELECT_SINGLE
                        return
                    fill = MOVE_COLOR
                    arrow = LAST
                except Exception:
                    self._mouseAction = ACTION_SELECT_SINGLE
                    return
            else:
                fill = RULER_COLOR
                arrow = BOTH
            self._vector = self.create_line(
                (i, j, i, j), fill=fill, arrow=arrow)
            self._vx0, self._vy0, self._vz0 = self.canvas2xyz(i, j)
            self._mouseAction = self.action

        # Move gantry to position
        elif self.action == ACTION_GANTRY:
            self.actionGantry(event.x, event.y)

        # Move gantry to position
        elif self.action == ACTION_WPOS:
            self.actionWPOS(event.x, event.y)

        # Add orientation marker
        elif self.action == ACTION_ADDORIENT:
            self.actionAddOrient(event.x, event.y)

        # Set coordinate origin
        elif self.action == ACTION_ORIGIN:
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            x, y, z = self.canvas2xyz(i, j)
            self.app.insertCommand(_("origin {:g} {:g} {:g}").format(x, y, z),
                                   True)
            self.setActionSelect()

        elif self.action == ACTION_PAN:
            self.pan(event)

    def midClick(self, event):
        self._mouseX = event.x
        self._mouseY = event.y
    
    def rightClick(self, event):
        self._mouseX = event.x
        self._mouseY = event.y
    
    def rotate(self, event):
        if (self._mouseX == event.x and self._mouseY == event.y):
            return
        
        RotAxis = normalize(vec4(event.y - self._mouseY, event.x - self._mouseX, 0, 0))
        
        RotAxis = inverse(self.MVMatrix) * RotAxis

        # Rotate about the Center of the screen
        rotationCenter = self.canvas2World(vec2(self.winfo_width() / 2., self.winfo_height() / 2.))

        self.MVMatrix = translate(self.MVMatrix, rotationCenter)

        self.MVMatrix = rotate(self.MVMatrix,
            0.01 * math.sqrt(pow(event.y - self._mouseY, 2) + math.pow(event.x - self._mouseX, 2)),
            vec3(RotAxis.x, RotAxis.y, RotAxis.z)) # type: ignore

        self.MVMatrix = translate(self.MVMatrix, -rotationCenter)
        
        self._mouseX = event.x
        self._mouseY = event.y
        
        self.cameraPosition()
        
        self.queueDraw()
        
    # ----------------------------------------------------------------------
    # Canvas motion button 1
    # ----------------------------------------------------------------------
    def buttonMotion(self, event):
        if self._mouseAction == ACTION_SELECT_AREA:
            self.updateSelectionRect(self._x, self._y, event.x, event.y)

        elif self._mouseAction in (ACTION_SELECT_SINGLE, ACTION_SELECT_DOUBLE):
            if abs(event.x - self._x) > 4 or abs(event.y - self._y) > 4:
                self._mouseAction = ACTION_SELECT_AREA
                self.updateSelectionRect(self._x, self._y, event.x, event.y)

        elif self._mouseAction in (ACTION_MOVE, ACTION_RULER):
            coords = self.coords(self._vector)
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            coords[-2] = i
            coords[-1] = j
            self.coords(self._vector, *coords)
            if self._mouseAction == ACTION_MOVE:
                self.move("sel", event.x - self._xp, event.y - self._yp)
                self.move("sel2", event.x - self._xp, event.y - self._yp)
                self.move("sel3", event.x - self._xp, event.y - self._yp)
                self.move("sel4", event.x - self._xp, event.y - self._yp)
                self._xp = event.x
                self._yp = event.y

            self._vx1, self._vy1, self._vz1 = self.canvas2xyz(i, j)
            dx = self._vx1 - self._vx0
            dy = self._vy1 - self._vy0
            dz = self._vz1 - self._vz0
            self.status(
                _("dx={:g}  dy={:g}  dz={:g}  length={:g}  angle={:g}").format(
                    dx,
                    dy,
                    dz,
                    math.sqrt(dx**2 + dy**2 + dz**2),
                    math.degrees(math.atan2(dy, dx)),
                )
            )

        elif self._mouseAction == ACTION_PAN:
            self.pan(event)

        self.setMouseStatus(event)

        self.queueDraw()
    
    def find_overlapping(self, x1, y1, x2, y2, lines):
        # Unit coordinates of the selection area boundaries
        xy1 = self.canvas2Unit(vec2(x1, y1))
        xy2 = self.canvas2Unit(vec2(x2, y2))

        xmin = min(xy1.x, xy2.x)
        xmax = max(xy1.x, xy2.x)
        ymin = min(xy1.y, xy2.y)
        ymax = max(xy1.y, xy2.y)
        
        # lines is a numpy array containing data for n lines
        # It has a size of 16·n, dtype=float32
        # It contains alternatively the starting and end point of a line in World coordinates.
        # A point is defined with 8 float32 numbers
        
        points = (numpy.reshape(lines, (-1, 8))[:, 1:4]).reshape((-1, 3))# x,y,z
        additionalColumn = numpy.ones((points.shape[0], 1), dtype=numpy.float32)
        
        points = numpy.hstack((points, additionalColumn)).reshape((-1, 4))

        # Change world coordinates of the line points to canvas unit coords
        MVP = numpy.array(self.PMatrix * self.MVMatrix)
        
        pointsCanvasUnit = (MVP @ points.T).T
        
        # Keep just x and y. Reshape to have starting and end point of each line in the same row
        linesCanvasUnit = pointsCanvasUnit[:, :2].reshape((-1, 4))
        
        
        # TODO: Mention the algorithm used here

        dx = linesCanvasUnit[:, 2] - linesCanvasUnit[:, 0]
        dy = linesCanvasUnit[:, 3] - linesCanvasUnit[:, 1]

        p = numpy.stack([-dx, dx, -dy, dy], axis=1)  # shape (N, 4)
        q = numpy.stack([linesCanvasUnit[:, 0] - xmin, xmax - linesCanvasUnit[:, 0],
                    linesCanvasUnit[:, 1] - ymin, ymax - linesCanvasUnit[:, 1]], axis=1)

        with numpy.errstate(divide='ignore', invalid='ignore'):
            r = q / p  # shape (N, 4)

        # Identify conditions
        mask_neg = p < 0
        mask_pos = p > 0
        mask_zero_and_q_neg = (p == 0) & (q < 0)
        any_outside = numpy.any(mask_zero_and_q_neg, axis=1)

        # Initialize u1 and u2
        u1 = numpy.where(mask_neg, r, 0.0)
        u2 = numpy.where(mask_pos, r, 1.0)

        u1_max = numpy.max(u1, axis=1)
        u2_min = numpy.min(u2, axis=1)

        intersects = (u1_max <= u2_min) & ~any_outside
        
        # Get the ids of the overlapped lines (id is the 1st parameter of the lines array)
        lineIds = lines.reshape((-1, 16))[:, 0]
        
        selectedIds = numpy.unique(lineIds[intersects]).tolist()
        
        return selectedIds
        
        
        
    # ----------------------------------------------------------------------
    # Canvas release button1. Select area
    # ----------------------------------------------------------------------
    def release(self, event):
        if self._mouseAction in (
            ACTION_SELECT_SINGLE,
            ACTION_SELECT_DOUBLE,
            ACTION_SELECT_AREA,
        ):
            closest = numpy.array([])
            
            if self._mouseAction == ACTION_SELECT_AREA:
                if self._x < event.x:  # From left->right enclosed
                    try:
                        closest = self.find_enclosed(
                            self.canvasx(self._x),
                            self.canvasy(self._y),
                            self.canvasx(event.x),
                            self.canvasy(event.y),
                        )
                    except Exception:
                        pass

                else:  # From right->left overlapping
                    try:
                        closest = self.find_overlapping(
                            self._x,
                            self._y,
                            event.x,
                            event.y,
                            self.pathLines
                        )
                    except Exception:
                        pass

                items = []
                for i in closest:
                    try:
                        items.append(self._items[i])
                    except Exception:
                        pass

            elif self._mouseAction in (ACTION_SELECT_SINGLE,
                                       ACTION_SELECT_DOUBLE):
                try:
                    closest = self.find_closest(
                        self.canvasx(event.x),
                        self.canvasy(event.y),
                        CLOSE_DISTANCE
                    )
                except Exception:
                    pass

                items = []
                for i in closest:
                    try:
                        items.append(self._items[i])
                    except KeyError:
                        tags = self.gettags(i)
                        if "Orient" in tags:
                            self.selectMarker(i)
                            return
                        pass
            if items:
                self.app.select(
                    items,
                    self._mouseAction == ACTION_SELECT_DOUBLE,
                    event.state & CONTROL_MASK == 0,
                )

            self._mouseAction = None
            self.queueDraw()

        elif self._mouseAction == ACTION_MOVE:
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            self._vx1, self._vy1, self._vz1 = self.canvas2xyz(i, j)
            dx = self._vx1 - self._vx0
            dy = self._vy1 - self._vy0
            dz = self._vz1 - self._vz0
            self.status(_("Move by {:g}, {:g}, {:g}").format(dx, dy, dz))
            self.app.insertCommand(("move %g %g %g") % (dx, dy, dz), True)

        elif self._mouseAction == ACTION_PAN:
            self.panRelease(event)

    # ----------------------------------------------------------------------
    def double(self, event):
        self._mouseAction = ACTION_SELECT_DOUBLE

    # ----------------------------------------------------------------------
    def motion(self, event):
        self.setMouseStatus(event)

    # -----------------------------------------------------------------------
    # Testing routine
    # -----------------------------------------------------------------------
    def __test(self, event):
        i = self.canvasx(event.x)
        j = self.canvasy(event.y)
        x, y, z = self.canvas2xyz(i, j)

    # ----------------------------------------------------------------------
    # Snap to the closest point if any
    # ----------------------------------------------------------------------
    def snapPoint(self, cx, cy):
        xs, ys = None, None
        if CNC.inch:
            dmin = (self.zoom / 25.4) ** 2  # 1mm maximum distance ...
        else:
            dmin = (self.zoom) ** 2
        dmin = (CLOSE_DISTANCE * self.zoom) ** 2

        # ... and if we are closer than 5pixels
        for item in self.find_closest(cx, cy, CLOSE_DISTANCE):
            try:
                bid, lid = self._items[item]
            except KeyError:
                continue

            # Very cheap and inaccurate approach :)
            coords = self.coords(item)
            x = coords[0]  # first
            y = coords[1]  # point
            d = (cx - x) ** 2 + (cy - y) ** 2
            if d < dmin:
                dmin = d
                xs, ys = x, y

            x = coords[-2]  # last
            y = coords[-1]  # point
            d = (cx - x) ** 2 + (cy - y) ** 2
            if d < dmin:
                dmin = d
                xs, ys = x, y

            # I need to check the real code and if
            # an arc check also the center?

        if xs is not None:
            return xs, ys
        else:
            return cx, cy

    # ----------------------------------------------------------------------
    # Get margins of selected items
    # ----------------------------------------------------------------------
    def getMargins(self):
        bbox = self.bbox("sel")
        if not bbox:
            return None
        x1, y1, x2, y2 = bbox
        dx = (x2 - x1 - 1) / self.zoom
        dy = (y2 - y1 - 1) / self.zoom
        return dx, dy

    # ----------------------------------------------------------------------
    def xview(self, *args):
        ret = Canvas.xview(self, *args)
        if args:
            self.cameraPosition()
        return ret

    # ----------------------------------------------------------------------
    def yview(self, *args):
        ret = Canvas.yview(self, *args)
        if args:
            self.cameraPosition()
        return ret

    # ----------------------------------------------------------------------
    def configureEvent(self, event):
        width = self.winfo_width()
        height = self.winfo_height()
        
        self.PMatrix = ortho(-width / 2.0 / self.zoom, 
                             width / 2.0 / self.zoom, 
                             -height / 2.0 / self.zoom,
                             height / 2.0 / self.zoom, 
                             -10000,
                             10000)
        self.cameraPosition()
        self.queueDraw()

    # ----------------------------------------------------------------------
    def pan(self, event):
        if self._mouseAction != ACTION_PAN:
            self.config(cursor=mouseCursor(ACTION_PAN))
            self._mouseAction = ACTION_PAN
            
        self.pan_delta(event.x - self._mouseX, event.y - self._mouseY)
        
        self._mouseX = event.x
        self._mouseY = event.y

    def pan_delta(self, deltaX, deltaY):
        # Pan a number of pixels in X and/or Y
        width = self.winfo_width()
        height = self.winfo_height()
        
        MVPinv = inverse(self.PMatrix * self.MVMatrix)
        
        pointFrom = MVPinv * vec4(-1, 1, 0, 1) # Screen (0, 0)
        pointTo = MVPinv * vec4(2 * (deltaX - width / 2.0) / width, 2 * (height / 2.0 - deltaY) / height, 0, 1) # Screen (deltaX, deltaY)

        self.MVMatrix = translate(self.MVMatrix, vec3((pointTo - pointFrom).x, (pointTo - pointFrom).y, (pointTo - pointFrom).z)) # type: ignore
        
        self.cameraPosition()
        
        self.queueDraw()
    # ----------------------------------------------------------------------
    def panRelease(self, event):
        self._mouseAction = None
        self.config(cursor=mouseCursor(self.action))

    # ----------------------------------------------------------------------
    def panLeft(self, event=None):
        self.pan_delta(15, 0) # 15 pixels, as in the original canvas

    def panRight(self, event=None):
        self.pan_delta(-15, 0)

    def panUp(self, event=None):
        self.pan_delta(0, 15)

    def panDown(self, event=None):
        self.pan_delta(0, -15)

    def canvas2Unit(self, coords : vec2):
        # Map screen pixel coordinates to opengl screen coords [-1.0 -> 1.0]
        # In OpenGL, y goes positive upwards
        width = self.winfo_width()
        height = self.winfo_height()
        
        return vec2(
            coords.x / (width / 2.0) - 1,
            1 - coords.y / (height / 2.0)
        )
    
    def canvas2World(self, coords : vec2) -> vec3:
        coordsUnit = self.canvas2Unit(coords)
        
        MVPinv = inverse(self.PMatrix * self.MVMatrix)
        
        return (MVPinv * vec4(coordsUnit, 0, 1)).xyz
    
    # ----------------------------------------------------------------------
    # Delay zooming to cascade multiple zoom actions
    # ----------------------------------------------------------------------
    def zoomCanvas(self, x, y, zoom):
        self._tx = x
        self._ty = y
        self.__tzoom *= zoom
        self.after_idle(self._zoomCanvas)

    # ----------------------------------------------------------------------
    # Zoom on screen position x,y by a factor zoom
    # ----------------------------------------------------------------------
    def _zoomCanvas(self, event=None):  # x, y, zoom):
        x = self._tx
        y = self._ty
        zoom = self.__tzoom

        self.__tzoom = 1.0

        width = self.winfo_width()
        height = self.winfo_height()     
        
        MVP = self.PMatrix * self.MVMatrix          
        
        # We zoom around the (x, y) screen location 
        zoomOrigin3d = self.canvas2World(vec2(x, y))
        
        screenCenter3d = (inverse(MVP) * vec4(0, 0, 0, 1)).xyz
        
        # Vector from zoom origin to projected center
        vZoomOriginToCenter = screenCenter3d - zoomOrigin3d
        
        # Translate the model, so that the origin keeps fixed when zooming
        self.MVMatrix = translate(self.MVMatrix, vZoomOriginToCenter * (1- 1/zoom))
        

        # Zoom around the mouse location
        
        self.zoom *= zoom
        
        self.PMatrix = ortho(-width / 2.0 / self.zoom, 
                             width / 2.0 / self.zoom, 
                             -height / 2.0 / self.zoom,
                             height / 2.0 / self.zoom, 
                             -10000,
                             10000)
        
        self.queueDraw()
        
        # TODO: Implement the rest
        return

        x0 = self.canvasx(0)
        y0 = self.canvasy(0)

        for i in self.find_all():
            self.scale(i, 0, 0, zoom, zoom)

        # Update last insert
        if self._lastGantry:
            self.updateGantry(*self.plotCoords([self._lastGantry])[0])
        else:
            self.updateGantry(0, 0)

        self._updateScrollBars()
        x0 -= self.canvasx(0)
        y0 -= self.canvasy(0)

        # Perform pin zoom
        dx = self.canvasx(x) * (1.0 - zoom)
        dy = self.canvasy(y) * (1.0 - zoom)

        # Drag to new location to center viewport
        self.scan_mark(0, 0)
        self.scan_dragto(int(round(dx - x0)), int(round(dy - y0)), 1)

        # Resize probe image if any
        if self._probe:
            self._projectProbeImage()
            self.itemconfig(self._probe, image=self._probeTkImage)
        self.cameraUpdate()

    # ----------------------------------------------------------------------
    # Return selected objects bounding box
    # ----------------------------------------------------------------------
    def selBbox(self):
        x1 = None
        for tag in ("sel", "sel2", "sel3", "sel4"):
            bb = self.bbox(tag)
            if bb is None:
                continue
            elif x1 is None:
                x1, y1, x2, y2 = bb
            else:
                x1 = min(x1, bb[0])
                y1 = min(y1, bb[1])
                x2 = max(x2, bb[2])
                y2 = max(y2, bb[3])

        if x1 is None:
            return self.bbox("all")
        return x1, y1, x2, y2

    # ----------------------------------------------------------------------
    # Zoom to Fit to Screen
    # ----------------------------------------------------------------------

    # New approach by onekk https://github.com/vlachoudis/bCNC/issues/1311
    def fit2Screen(self, event=None):
        """Zoom to Fit to Screen"""
        # Modify translation of the ModelView Matrix to -modelCenter
        #self.MVMatrix[3][0] = self.MVMatrix[3][1] = self.MVMatrix[3][2] = 0
        #self.MVMatrix[3] = vec4(-self._modelCenter, 1)
        upVector = inverse(self.MVMatrix) * vec4(0, 1, 0, 0)
        depthVector = inverse(self.MVMatrix) * vec4(0, 0, 1, 0)
        
        self.MVMatrix = lookAt(
            self._modelCenter + depthVector.xyz, # eye
            self._modelCenter, # target
            upVector.xyz # up
            )
        # Adjust the Projection Matrix
        width = self.winfo_width()
        height = self.winfo_height()
        
        self.zoom = min(width, height) / self._modelSize  # TODO: calculate based on model size
        
        self.PMatrix = ortho(-width / 2.0 / self.zoom, 
                             width / 2.0 / self.zoom, 
                             -height / 2.0 / self.zoom,
                             height / 2.0 / self.zoom, 
                             -10000,
                             10000)

        self.cameraPosition()
        self.queueDraw()

    def fit2Screen_old(self, event=None):
        bb = self.selBbox()
        if bb is None:
            return
        x1, y1, x2, y2 = bb

        try:
            zx = float(self.winfo_width()) / (x2 - x1)
        except Exception:
            return
        try:
            zy = float(self.winfo_height()) / (y2 - y1)
        except Exception:
            return
        if zx > 1.0:
            self.__tzoom = min(zx, zy)
        else:
            self.__tzoom = max(zx, zy)

        self._tx = self._ty = 0
        self._zoomCanvas()

        # Find position of new selection
        x1, y1, x2, y2 = self.selBbox()
        xm = (x1 + x2) // 2
        ym = (y1 + y2) // 2
        sx1, sy1, sx2, sy2 = map(float, self.cget("scrollregion").split())
        midx = float(xm - sx1) / (sx2 - sx1)
        midy = float(ym - sy1) / (sy2 - sy1)

        a, b = self.xview()
        d = (b - a) / 2.0
        self.xview_moveto(midx - d)

        a, b = self.yview()
        d = (b - a) / 2.0
        self.yview_moveto(midy - d)

        self.cameraPosition()

    # ----------------------------------------------------------------------
    def menuZoomIn(self, event=None):
        x = self.winfo_width() // 2
        y = self.winfo_height() // 2
        self.zoomCanvas(x, y, 2.0)

    # ----------------------------------------------------------------------
    def menuZoomOut(self, event=None):
        x = self.winfo_width() // 2
        y = self.winfo_height() // 2
        self.zoomCanvas(x, y, 0.5)

    # ----------------------------------------------------------------------
    def mouseZoomIn(self, event):
        self.zoomCanvas(event.x, event.y, ZOOM)

    # ----------------------------------------------------------------------
    def mouseZoomOut(self, event):
        self.zoomCanvas(event.x, event.y, 1.0 / ZOOM)

    # ----------------------------------------------------------------------
    def wheel(self, event):
        self.zoomCanvas(event.x, event.y, pow(ZOOM, (event.delta // 120)))

    # ----------------------------------------------------------------------
    # Change the insert marker location
    # ----------------------------------------------------------------------
    def activeMarker(self, item):
        if item is None:
            return
        b, i = item
        if i is None:
            return
        block = self.gcode[b]
        item = block.path(i)

        if item is not None and item != self._lastActive:
            if self._lastActive is not None:
                self.itemconfig(self._lastActive, arrow=NONE)
            self._lastActive = item
            self.itemconfig(self._lastActive, arrow=LAST)

    # ----------------------------------------------------------------------
    # Display gantry
    # ----------------------------------------------------------------------
    def gantry(self, wx, wy, wz, mx, my, mz):
        self._lastGantry = (wx, wy, wz)
        self.updateGantry(wx, wy, wz)
        if self._cameraImage and self.cameraAnchor == NONE:
            self.cameraPosition()

        dx = wx - mx
        dy = wy - my
        dz = wz - mz
        if (
            abs(dx - self._dx) > 0.0001
            or abs(dy - self._dy) > 0.0001
            or abs(dz - self._dz) > 0.0001
        ):
            self._dx = dx
            self._dy = dy
            self._dz = dz

            if not self.draw_workarea:
                return
            
            self.updateWorkArea()

    # ----------------------------------------------------------------------
    # Clear highlight of selection
    # ----------------------------------------------------------------------
    def clearSelection(self):
        if self._lastActive is not None:
            # TODO: self.itemconfig(self._lastActive, arrow=NONE)
            self._lastActive = None
        
        self.deselectAll(self.pathLines, self.pathVBO)
        """ for i in SELECTION_TAGS:
            self.dtag(i)
        self.delete("info") """

    # ----------------------------------------------------------------------
    # Highlight selected items
    # ----------------------------------------------------------------------
    def select(self, items):
        linesAndFlags = []
        
        for b, i in items:
            block = self.gcode[b]
            flags = FLAG_SELECTED | (FLAG_ENABLED if block.enable else 0)
            
            if i is None:
                for path in block._path:
                    if path is not None:
                        linesAndFlags.append([path, flags])

            elif isinstance(i, int):
                path = block.path(i)
                if path:
                    linesAndFlags.append([path, flags])

        """ 
            self.tag_raise(i) """
        
        self.setFlags(self.pathLines, FLAG_SELECTED | FLAG_ENABLED, linesAndFlags, self.pathVBO)
                
        self.updateMargin()
    
    def setFlags(self, linesArray, flagsToModify, linesAndFlags, bufferToUpdate = None):
        # linesAndTags must be an array of arrays (nx2)
        # The first item of each array is the line number, and the second item the value with the Tags to be activated
        selections = numpy.array(linesAndFlags, dtype=numpy.float32).reshape((-1, 2))
        lookup = dict(selections)
        
        linesArray16 = linesArray.reshape((-1, 16))
        mask = numpy.isin(linesArray16[:, 0], selections[:, 0])
        
        matched_keys = linesArray16[mask, 0]
        
        # Since linesArray16 is a reshaped view of linesArray, changes are reflected in the original array
        # First, clear the bits
        linesArray16[mask, 7] = linesArray16[mask, 7].astype(int) & ~flagsToModify
        linesArray16[mask, 15] = linesArray16[mask, 15].astype(int) & ~flagsToModify
        # Then, set the ones to modify
        if matched_keys.size > 0:
            linesArray16[mask, 7] = linesArray16[mask, 7].astype(int) | ((numpy.vectorize(lookup.get)(matched_keys)).astype(int) & flagsToModify)
            linesArray16[mask, 15] = linesArray16[mask, 15].astype(int) | ((numpy.vectorize(lookup.get)(matched_keys)).astype(int) & flagsToModify)
        
            if bufferToUpdate:
                glBindBuffer(GL_ARRAY_BUFFER, bufferToUpdate)
                glBufferSubData(GL_ARRAY_BUFFER, 0, linesArray.nbytes, linesArray)
                glBindBuffer(GL_ARRAY_BUFFER, 0)
                self.queueDraw()

    def deletePaths(self):
        self.lines.clear()
        self.update_buffer(self.pathVBO, self.lines)

    def deselectAll(self, linesArray, bufferToUpdate = None):
        linesArray16 = linesArray.reshape((-1, 16))
        
        linesArray16[:, 7] = linesArray16[:, 7].astype(int) & ~FLAG_SELECTED
        linesArray16[:, 15] = linesArray16[:, 15].astype(int) & ~FLAG_SELECTED
        
        if bufferToUpdate:
            glBindBuffer(GL_ARRAY_BUFFER, bufferToUpdate)
            glBufferSubData(GL_ARRAY_BUFFER, 0, linesArray.nbytes, linesArray)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
            self.queueDraw()
    
    # ----------------------------------------------------------------------
    # Select orientation marker
    # ----------------------------------------------------------------------
    def selectMarker(self, item):
        # find marker
        for i, paths in enumerate(self.gcode.orient.paths):
            if item in paths:
                self._orientSelected = i
                for j in paths:
                    self.itemconfig(j, width=2)
                self.event_generate("<<OrientSelect>>", data=i)
                return
        self._orientSelected = None

    # ----------------------------------------------------------------------
    # Highlight marker that was selected
    # ----------------------------------------------------------------------
    def orientChange(self, marker):
        self.itemconfig("Orient", width=1)
        if marker >= 0:
            self._orientSelected = marker
            try:
                for i in self.gcode.orient.paths[self._orientSelected]:
                    self.itemconfig(i, width=2)
            except IndexError:
                self.drawOrient()
        else:
            self._orientSelected = None

    # ----------------------------------------------------------------------
    # Display graphical information on selected blocks
    # ----------------------------------------------------------------------
    def showInfo(self, blocks):
        self.delete("info")  # clear any previous information
        for bid in blocks:
            block = self.gcode.blocks[bid]
            xyz = [
                (block.xmin, block.ymin, 0.0),
                (block.xmax, block.ymin, 0.0),
                (block.xmax, block.ymax, 0.0),
                (block.xmin, block.ymax, 0.0),
                (block.xmin, block.ymin, 0.0),
            ]
            self.create_line(self.plotCoords(xyz), fill=INFO_COLOR, tag="info")
            xc = (block.xmin + block.xmax) / 2.0
            yc = (block.ymin + block.ymax) / 2.0
            r = min(block.xmax - xc, block.ymax - yc)
            closed, direction = self.gcode.info(bid)

            if closed == 0:  # open path
                if direction == 1:
                    sf = math.pi / 4.0
                    ef = 2.0 * math.pi - sf
                else:
                    ef = math.pi / 4.0
                    sf = 2.0 * math.pi - ef
            elif closed == 1:
                if direction == 1:
                    sf = 0.0
                    ef = 2.0 * math.pi
                else:
                    ef = 0.0
                    sf = 2.0 * math.pi

            elif closed is None:
                continue

            n = 64
            df = (ef - sf) / float(n)
            xyz = []
            f = sf
            for i in range(n + 1):
                xyz.append(
                    (xc + r * math.sin(f), yc + r * math.cos(f), 0.0)
                )  # towards up
                f += df
            self.create_line(
                self.plotCoords(xyz),
                fill=INFO_COLOR,
                width=5,
                arrow=LAST,
                arrowshape=(32, 40, 12),
                tag="info",
            )

    # -----------------------------------------------------------------------
    def cameraOn(self, event=None):
        if not self.camera.start():
            return
        self.cameraRefresh()

    # -----------------------------------------------------------------------
    def cameraOff(self, event=None):
        return # TODO: implement this function
        self.delete(self._cameraImage)
        self.delete(self._cameraHori)
        self.delete(self._cameraVert)
        self.delete(self._cameraCircle)
        self.delete(self._cameraCircle2)

        self._cameraImage = None
        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None
        self.camera.stop()

    # -----------------------------------------------------------------------
    def cameraUpdate(self):
        if not self.camera.isOn():
            return
        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None
        self.cameraRefresh()
        self.cameraPosition()

    # -----------------------------------------------------------------------
    def cameraRefresh(self):
        if not self.camera.read():
            self.cameraOff()
            return
        self.camera.rotation = self.cameraRotation
        self.camera.xcenter = self.cameraXCenter
        self.camera.ycenter = self.cameraYCenter
        if self.cameraEdge:
            self.camera.canny(50, 200)
        if self.cameraAnchor == NONE or self.zoom / self.cameraScale > 1.0:
            self.camera.resize(
                self.zoom / self.cameraScale,
                self._cameraMaxWidth,
                self._cameraMaxHeight,
            )
        if self._cameraImage is None:
            self._cameraImage = self.create_image((0, 0), tag="CameraImage")
            self.lower(self._cameraImage)
            # create cross hair at dummy location we will correct latter
            self._cameraHori = self.create_line(
                0, 0, 1, 0, fill=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraVert = self.create_line(
                0, 0, 0, 1, fill=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraCircle = self.create_oval(
                0, 0, 1, 1, outline=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraCircle2 = self.create_oval(
                0, 0, 1, 1, outline=CAMERA_COLOR, dash=(3, 3), tag="CrossHair"
            )
            self.cameraPosition()
        try:
            self.itemconfig(self._cameraImage, image=self.camera.toTk())
        except Exception:
            pass
        self._cameraAfter = self.after(100, self.cameraRefresh)

    # -----------------------------------------------------------------------
    def cameraFreeze(self, freeze):
        if self.camera.isOn():
            self.camera.freeze(freeze)

    # -----------------------------------------------------------------------
    def cameraSave(self, event=None):
        try:
            self._count += 1
        except Exception:
            self._count = 1
        self.camera.save("camera%02d.png" % (self._count))

    # ----------------------------------------------------------------------
    # Reposition camera and crosshair
    # ----------------------------------------------------------------------
    def cameraPosition(self):
        # TODO: Implement this function
        return
    
        if self._cameraImage is None:
            return
        w = self.winfo_width()
        h = self.winfo_height()
        hc, wc = self.camera.image.shape[:2]
        wc //= 2
        hc //= 2
        x = w // 2  # everything on center
        y = h // 2
        if self.cameraAnchor is NONE:
            if self._lastGantry is not None:
                x, y = self.plotCoords([self._lastGantry])[0]
            else:
                x = y = 0
            if not self.cameraSwitch:
                x += self.cameraDx * self.zoom
                y -= self.cameraDy * self.zoom
            r = self.cameraR * self.zoom
        else:
            if self.cameraAnchor != CENTER:
                if N in self.cameraAnchor:
                    y = hc
                elif S in self.cameraAnchor:
                    y = h - hc
                if W in self.cameraAnchor:
                    x = wc
                elif E in self.cameraAnchor:
                    x = w - wc
            x = self.canvasx(x)
            y = self.canvasy(y)
            if self.zoom / self.cameraScale > 1.0:
                r = self.cameraR * self.zoom
            else:
                r = self.cameraR * self.cameraScale

        self.coords(self._cameraImage, x, y)
        self.coords(self._cameraHori, x - wc, y, x + wc, y)
        self.coords(self._cameraVert, x, y - hc, x, y + hc)
        self.coords(self._cameraCircle, x - r, y - r, x + r, y + r)
        self.coords(
            self._cameraCircle2, x - r * 2, y - r * 2, x + r * 2, y + r * 2)

    # ----------------------------------------------------------------------
    # Crop center of camera and search it in subsequent movements
    # ----------------------------------------------------------------------
    def cameraMakeTemplate(self, r):
        if self._cameraImage is None:
            return
        self._template = self.camera.getCenterTemplate(r)

    # ----------------------------------------------------------------------
    def cameraMatchTemplate(self):
        return self.camera.matchTemplate(self._template)

    # ----------------------------------------------------------------------
    # Parse and draw the file from the editor to g-code commands
    # ----------------------------------------------------------------------
    def draw(self):
        self.make_current()
        width, height = self.winfo_width(), self.winfo_height()
        glViewport(0, 0, width, height)
        
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT) # type: ignore
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        glDisable(GL_DEPTH_TEST)
        glEnable(GL_BLEND)
        glEnable(GL_LINE_SMOOTH)
        glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
        glEnable(GL_CULL_FACE)
        
        # Draw background
        glUseProgram(self.backgroundProgram)
        glBindBuffer(GL_ARRAY_BUFFER, self.backgroundVBO)
        glVertexAttribPointer(glGetAttribLocation(self.backgroundProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, 6*4, c_void_p(0*4))
        glVertexAttribPointer(glGetAttribLocation(self.backgroundProgram, "color"), 3, GL_FLOAT, GL_FALSE, 6*4, c_void_p(3*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.backgroundProgram, "xyz"))
        glEnableVertexAttribArray(glGetAttribLocation(self.backgroundProgram, "color"))
        glDrawArrays(GL_TRIANGLES, 0, 6)

        # Draw grid
        if self.draw_grid:
            glUseProgram(self.gridProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.gridVBO)
            PARAMETERS_PER_VERTEX = 4
            glVertexAttribPointer(glGetAttribLocation(self.axesProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glVertexAttribPointer(glGetAttribLocation(self.axesProgram, "position"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
            glEnableVertexAttribArray(glGetAttribLocation(self.axesProgram, "xyz"))
            glEnableVertexAttribArray(glGetAttribLocation(self.axesProgram, "position"))
            
            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.axesProgram, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
            
            zoom_loc = glGetUniformLocation(program=self.axesProgram, name="zoom")
            glUniform1f(zoom_loc, self.zoom)
            
            glLineWidth(2)
            glEnable(GL_LINE_SMOOTH)
            glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
            glDrawArrays(GL_LINES, 0, len(self.gridVertices) // PARAMETERS_PER_VERTEX)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
            
        # Draw margins
        if self.draw_margin:
            self.drawLines(self.marginVertices, self.marginsVBO, 1)
        
        # Draw work area
        if self.draw_workarea:
            self.drawLines(self.workAreaVertices, self.workAreaVBO, 1)
        
        # Draw path
        if self.pathLines.size > 0:
            glEnable(GL_DEPTH_TEST)
            glUseProgram(self.shader_program)
            glBindBuffer(GL_ARRAY_BUFFER, self.pathVBO)
            PARAMETERS_PER_VERTEX = 8
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "id"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(1*4))
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "length"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(4*4))
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "colorValue"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(5*4))
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "dashRatio"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(6*4))
            glVertexAttribPointer(glGetAttribLocation(self.shader_program, "flags"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(7*4))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "id"))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "xyz"))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "length"))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "colorValue"))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "dashRatio"))
            glEnableVertexAttribArray(glGetAttribLocation(self.shader_program, "flags"))


            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.shader_program, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

            glLineWidth(2)
            glDrawArrays(GL_LINES, 0, len(self.pathLines) // PARAMETERS_PER_VERTEX)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        # Draw axes
        if self.draw_axes:
            glDisable(GL_DEPTH_TEST)
            glUseProgram(self.axesProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.axesVBO)
            PARAMETERS_PER_VERTEX = 5
            glVertexAttribPointer(glGetAttribLocation(self.axesProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glVertexAttribPointer(glGetAttribLocation(self.axesProgram, "position"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
            glVertexAttribPointer(glGetAttribLocation(self.axesProgram, "axis"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(4*4))
            glEnableVertexAttribArray(glGetAttribLocation(self.axesProgram, "xyz"))
            glEnableVertexAttribArray(glGetAttribLocation(self.axesProgram, "position"))
            glEnableVertexAttribArray(glGetAttribLocation(self.axesProgram, "axis"))
            
            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.axesProgram, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
            
            zoom_loc = glGetUniformLocation(program=self.axesProgram, name="zoom")
            glUniform1f(zoom_loc, self.zoom)
            
            glLineWidth(2)
            glEnable(GL_LINE_SMOOTH)
            glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
            glDrawArrays(GL_LINES, 0, len(self.axesVertices) // PARAMETERS_PER_VERTEX)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        # Draw gantry
        glUseProgram(self.gantryProgram)
        glBindBuffer(GL_ARRAY_BUFFER, self.gantryVBO)
        PARAMETERS_PER_VERTEX = 6
        glVertexAttribPointer(glGetAttribLocation(self.gantryProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.gantryProgram, "normal"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.gantryProgram, "xyz"))
        glEnableVertexAttribArray(glGetAttribLocation(self.gantryProgram, "normal"))
        
        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.gantryProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
        
        location_loc = glGetUniformLocation(program=self.gantryProgram, name="location")
        glUniform3fv(location_loc, 1, value_ptr(self._gantryLocation))
        
        light1dir = normalize(inverse(MVP) * vec4(1.0, -0.25, -1.0, 0)).xyz
        light2dir = normalize(inverse(MVP) * vec4(-0.5, -0.125, -0.5, 0)).xyz
        
        light1dir_loc = glGetUniformLocation(program=self.gantryProgram, name="light1dir")
        glUniform3fv(light1dir_loc, 1, value_ptr(light1dir))
        light2dir_loc = glGetUniformLocation(program=self.gantryProgram, name="light2dir")
        glUniform3fv(light2dir_loc, 1, value_ptr(light2dir))
        
        glLineWidth(2)
        glEnable(GL_LINE_SMOOTH)
        glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
        glDrawArrays(GL_TRIANGLES, 0, len(self.gantryVertices) // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        # Draw selection rectangle
        if self._mouseAction == ACTION_SELECT_AREA:
            glDisable(GL_CULL_FACE)
            glUseProgram(self.SelectionRectProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.SelectionRectVBO)
            PARAMETERS_PER_VERTEX = 2
            glVertexAttribPointer(glGetAttribLocation(self.SelectionRectProgram, "uv"), 2, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glEnableVertexAttribArray(glGetAttribLocation(self.SelectionRectProgram, "uv"))
            
            # Selection to the right -> Blue. To the left -> Green
            if self.SelectionRectVertices[2] > self.SelectionRectVertices[0]:
                rect_color = vec3(0, 0, 1)
            else:
                rect_color = vec3(0, 1, 0)
            color_loc = glGetUniformLocation(program=self.SelectionRectProgram, name="color")
            glUniform3fv(color_loc, 1, value_ptr(rect_color))
            
            glLineWidth(2)
            glEnable(GL_LINE_SMOOTH)
            glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
            
            glDrawArrays(GL_TRIANGLES, 0, len(self.SelectionRectVertices) // PARAMETERS_PER_VERTEX)
            glBindBuffer(GL_ARRAY_BUFFER, 0)


        glUseProgram(0)
        
        self.swap_buffers()
        
        self._drawRequested = False
    
    def drawLines(self, vertices, vbo, lineWidth):
        glUseProgram(self.linesProgram)
        glBindBuffer(GL_ARRAY_BUFFER, vbo)
        PARAMETERS_PER_VERTEX = 9
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "color"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "dash"), 2, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(6*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "position"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(8*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "xyz"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "color"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "dash"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "position"))
        
        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.linesProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
        
        zoom_loc = glGetUniformLocation(program=self.linesProgram, name="zoom")
        glUniform1f(zoom_loc, self.zoom)
        
        glLineWidth(lineWidth)
        glEnable(GL_LINE_SMOOTH)
        glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
        glDrawArrays(GL_LINES, 0, len(vertices) // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
    
    def queueDraw(self):
        if self._drawRequested:
            return
        
        self._drawRequested = True
        
        self.after('idle', self.draw)
        
    def updateAll(self, view=None):

        self.make_current()
        
        self._last = (0.0, 0.0, 0.0)
        self.initPosition()
        
        self.createPaths()
        self.update_buffer(self.pathVBO, self.lines)
        self.updateGrid()
        self.createAxes()
        self.updateMargin()
        self.updateWorkArea()

        """ self.__tzoom = 1.0
        xyz = self.canvas2xyz(
            self.canvasx(self.winfo_width() / 2),
            self.canvasy(self.winfo_height() / 2)
        )

        if view is not None:
            self.view = view

        self.drawPaths()
        self.drawProbe()
        self.drawOrient()

        ij = self.plotCoords([xyz])[0]
        dx = int(round(self.canvasx(self.winfo_width() / 2) - ij[0]))
        dy = int(round(self.canvasy(self.winfo_height() / 2) - ij[1]))
        self.scan_mark(0, 0)
        self.scan_dragto(int(round(dx)), int(round(dy)), 1) """

        self.queueDraw()

    # ----------------------------------------------------------------------
    # Initialize gantry position
    # ----------------------------------------------------------------------
    def initPosition(self):
        
        # TODO: Anything apart from paths must be deleted...?
        #self.delete(ALL)
        self.deletePaths()
        
        self._cameraImage = None
        
        self.updateGantry(0, 0, 0)

        self._lastInsert = None
        self._lastActive = None
        self._vector = None
        self._items.clear()
        self.cnc.initPath()
        self.cnc.resetAllMargins()

    # ----------------------------------------------------------------------
    # Update gantry location
    # ----------------------------------------------------------------------
    def updateGantry(self, x, y, z):
        self._gantryLocation = vec3(x, y, z)
        
        gr = max(3, int(CNC.vars["diameter"] / 2.0))
        
        if self._gantryRadius == None or self._gantryRadius != gr:
            self._gantryRadius = gr
            gh = 3 * gr
            
            NUM_FACES = 32 # Number of faces in the whole turn of 360º
            
            # We create the gantry as a conical closed surface made up of triangles
            faceAngle = 2 * math.pi / NUM_FACES
            coneAngle = math.atan(gr / gh)
            
            vertices = []
            
            # We also calculate the normal vector for each vertex, in order to shade lights
            
            for f in range(NUM_FACES):
                # Lower Cone
                vertices.extend([
                    gr * math.cos(faceAngle * f),
                    gr * math.sin(faceAngle * f),
                    gh,
                    math.cos(coneAngle) * math.cos(faceAngle * f), math.cos(coneAngle) * math.sin(faceAngle * f), -math.sin(coneAngle)])
                vertices.extend([
                    0, 0, 0,
                    math.cos(coneAngle) * math.cos(faceAngle * f), math.cos(coneAngle) * math.sin(faceAngle * f), -math.sin(coneAngle)]) # normal
                vertices.extend([
                    gr * math.cos(faceAngle * (f+1)),
                    gr * math.sin(faceAngle * (f+1)),
                    gh,
                    math.cos(coneAngle) * math.cos(faceAngle * (f+1)), math.cos(coneAngle) * math.sin(faceAngle * (f+1)), -math.sin(coneAngle)])
                # Upper Disc
                vertices.extend([
                    0, 0, gh, 
                    0, 0, 1]) # Normal pointing upwards [0, 0, 1]
                vertices.extend([
                    gr * math.cos(faceAngle * f),
                    gr * math.sin(faceAngle * f),
                    gh,
                    0, 0, 1])
                vertices.extend([
                    gr * math.cos(faceAngle * (f+1)),
                    gr * math.sin(faceAngle * (f+1)),
                    gh,
                    0, 0, 1])
            
            self.gantryVertices = numpy.array(vertices, dtype=numpy.float32)
            
            glBindBuffer(GL_ARRAY_BUFFER, self.gantryVBO)
            glBufferData(GL_ARRAY_BUFFER, self.gantryVertices.nbytes, self.gantryVertices, GL_STATIC_DRAW)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Create system axes
    # ----------------------------------------------------------------------
    def createAxes(self):
        dx = CNC.vars["axmax"] - CNC.vars["axmin"]
        dy = CNC.vars["aymax"] - CNC.vars["aymin"]
        d = min(dx, dy)
        try:
            s = math.pow(10.0, int(math.log10(d)))
        except Exception:
            if CNC.inch:
                s = 10.0
            else:
                s = 100.0
        
        self.axesVertices = numpy.array([
            # X axis
            0, 0, 0, # Start Point
            0, # position. 0 for the first point of the line and length for the second. Used for dashed lines
            1, # Axis X
            s, 0, 0, # End Point
            s, # position. 0 for the first point of the line and length for the second. Used for dashed lines
            1, # Axis X
            # Y axis
            0, 0, 0, 0, 2, 0, s, 0, s, 2,
            # Z axis          
            0, 0, 0, 0, 3, 0, 0, s, s, 3
        ], dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.axesVBO)
        glBufferData(GL_ARRAY_BUFFER, self.axesVertices.nbytes, self.axesVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)

    # Update the selection rectangle
    def updateSelectionRect(self, x1, y1, x2, y2):
        glBindBuffer(GL_ARRAY_BUFFER, self.SelectionRectVBO)

        p1 = self.canvas2Unit(vec2(x1, y1))
        p2 = self.canvas2Unit(vec2(x2, y2))

        self.SelectionRectVertices = numpy.array(
            [p1.x, p1.y,
             p2.x, p1.y,
             p2.x, p2.y,
             p1.x, p1.y,
             p2.x, p2.y,
             p1.x, p2.y],
             dtype=numpy.float32)
        
        glBufferData(GL_ARRAY_BUFFER, self.SelectionRectVertices.nbytes, self.SelectionRectVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
    
    # ----------------------------------------------------------------------
    # Draw margins of selected blocks
    # ----------------------------------------------------------------------
    def updateMargin(self):
        if not self.draw_margin:
            self.queueDraw()
            return
        
        vertices = []

        if CNC.isMarginValid():
            vertices.extend([
                CNC.vars["xmin"], CNC.vars["ymin"], 0.0,    # xyz
                1, 0, 1,                                    # color
                1, 0,                                       # dash
                0,                                          # position. 0 for starting point and length for end point
                CNC.vars["xmax"], CNC.vars["ymin"], 0.0,
                0, 1, 0,
                1, 0,
                CNC.vars["xmax"] - CNC.vars["xmin"],
                
                CNC.vars["xmax"], CNC.vars["ymin"], 0.0,
                1, 0, 1,
                1, 0,
                0,
                CNC.vars["xmax"], CNC.vars["ymax"], 0.0,
                1, 0, 1,
                1, 0,
                CNC.vars["ymax"] - CNC.vars["ymin"],
                
                CNC.vars["xmax"], CNC.vars["ymax"], 0.0,
                1, 0, 1,
                1, 0,
                0,
                CNC.vars["xmin"], CNC.vars["ymax"], 0.0,
                1, 0, 1,
                1, 0,
                CNC.vars["xmax"] - CNC.vars["xmin"],
                
                CNC.vars["xmin"], CNC.vars["ymax"], 0.0,
                1, 0, 1,
                1, 0,
                0,
                CNC.vars["xmin"], CNC.vars["ymin"], 0.0,
                1, 0, 1,
                1, 0,
                CNC.vars["xmax"] - CNC.vars["xmin"]
            ])

        if not CNC.isAllMarginValid():
            self.queueDraw()
            return
        
        vertices.extend([
            CNC.vars["axmin"], CNC.vars["aymin"], 0.0,    # xyz
                1, 0, 1,                                    # color
                6, 4,                                       # dash
                0,                                          # position. 0 for starting point and length for end point
                CNC.vars["axmax"], CNC.vars["aymin"], 0.0,
                1, 0, 1,
                6, 4,
                CNC.vars["axmax"] - CNC.vars["axmin"],
                
                CNC.vars["axmax"], CNC.vars["aymin"], 0.0,
                1, 0, 1,
                6, 4,
                0,
                CNC.vars["axmax"], CNC.vars["aymax"], 0.0,
                1, 0, 1,
                6, 4,
                CNC.vars["aymax"] - CNC.vars["aymin"],
                
                CNC.vars["axmax"], CNC.vars["aymax"], 0.0,
                1, 0, 1,
                6, 4,
                0,
                CNC.vars["axmin"], CNC.vars["aymax"], 0.0,
                1, 0, 1,
                6, 4,
                CNC.vars["axmax"] - CNC.vars["axmin"],
                
                CNC.vars["axmin"], CNC.vars["aymax"], 0.0,
                1, 0, 1,
                6, 4,
                0,
                CNC.vars["axmin"], CNC.vars["aymin"], 0.0,
                1, 0, 1,
                6, 4,
                CNC.vars["axmax"] - CNC.vars["axmin"]
        ])

        self.marginVertices = numpy.array(vertices, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.marginsVBO)
        glBufferData(GL_ARRAY_BUFFER, self.marginVertices.nbytes, self.marginVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Change rectangle coordinates
    # ----------------------------------------------------------------------
    def _rectCoords(self, rect, xmin, ymin, xmax, ymax, z=0.0):
        self.coords(
            rect,
            tkinter._flatten(
                self.plotCoords(
                    [
                        (xmin, ymin, z),
                        (xmax, ymin, z),
                        (xmax, ymax, z),
                        (xmin, ymax, z),
                        (xmin, ymin, z),
                    ]
                )
            ),
        )

    # ----------------------------------------------------------------------
    # Draw a 3D path
    # ----------------------------------------------------------------------
    def _drawPath(self, path, z=0.0, **kwargs):
        xyz = []
        for segment in path:
            xyz.append((segment.A[0], segment.A[1], z))
            xyz.append((segment.B[0], segment.B[1], z))
        rect = (self.create_line(self.plotCoords(xyz), **kwargs),)
        return rect

    # ----------------------------------------------------------------------
    # Draw a 3D rectangle
    # ----------------------------------------------------------------------
    def _drawRect(self, xmin, ymin, xmax, ymax, z=0.0, **kwargs):
        xyz = [
            (xmin, ymin, z),
            (xmax, ymin, z),
            (xmax, ymax, z),
            (xmin, ymax, z),
            (xmin, ymin, z),
        ]
        rect = (self.create_line(self.plotCoords(xyz), **kwargs),)
        return rect

    # ----------------------------------------------------------------------
    # Draw a workspace rectangle
    # ----------------------------------------------------------------------
    def updateWorkArea(self):
        if not self.draw_workarea:
            self.queueDraw()
            return

        xmin = self._dx - CNC.travel_x
        ymin = self._dy - CNC.travel_y
        xmax = self._dx
        ymax = self._dy

        vertices = [
            xmin, ymin, 0.0,    # xyz
            1, 0.647, 0,        # color
            6, 4,               # dash (pixels on, pixels off)
            0,                  # position. 0 for starting point and length for end point
            xmax, ymin, 0.0,
            1, 0.647, 0,
            6, 4,
            xmax - xmin,
            
            xmax, ymin, 0.0, 1, 0.647, 0, 6, 4, 0, 
            xmax, ymax, 0.0, 1, 0.647, 0, 6, 4, ymax - ymin,
            
            xmax, ymax, 0.0, 1, 0.647, 0, 6, 4, 0,                 
            xmin, ymax, 0.0, 1, 0.647, 0, 6, 4, xmax - xmin,
            
            xmin, ymax, 0.0, 1, 0.647, 0, 6, 4, 0,                 
            xmin, ymin, 0.0, 1, 0.647, 0, 6, 4, ymax - ymin,
        ]

        self.workAreaVertices = numpy.array(vertices, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.workAreaVBO)
        glBufferData(GL_ARRAY_BUFFER, self.workAreaVertices.nbytes, self.workAreaVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Draw coordinates grid
    # ----------------------------------------------------------------------
    def updateGrid(self):
        vertices = []
        
        xmin = (CNC.vars["axmin"] // 10) * 10
        xmax = (CNC.vars["axmax"] // 10 + 1) * 10
        ymin = (CNC.vars["aymin"] // 10) * 10
        ymax = (CNC.vars["aymax"] // 10 + 1) * 10
        
        for i in range(
            int(CNC.vars["aymin"] // 10), int(CNC.vars["aymax"] // 10) + 2
        ):
            y = i * 10.0
            vertices.extend([
                xmin, y, 0, # Line starting point
                0,          # Position. 0 for the starting point
                xmax, y, 0, # Line end point
                xmax - xmin # Position. Length for the end point
            ])

        for i in range(
            int(CNC.vars["axmin"] // 10), int(CNC.vars["axmax"] // 10) + 2
        ):
            x = i * 10.0
            vertices.extend([
                x, ymin, 0,
                0,
                x, ymax, 0,
                ymax - ymin
            ])
        
        self.gridVertices = numpy.array(vertices, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.gridVBO)
        glBufferData(GL_ARRAY_BUFFER, self.gridVertices.nbytes, self.gridVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Display orientation markers
    # ----------------------------------------------------------------------
    def drawOrient(self, event=None):
        self.delete("Orient")
        if self.view in (VIEW_XZ, VIEW_YZ):
            return

        # Draw orient markers
        if CNC.inch:
            w = 0.1
        else:
            w = 2.5

        self.gcode.orient.clearPaths()
        for i, (xm, ym, x, y) in enumerate(self.gcode.orient.markers):
            paths = []
            # Machine position (cross)
            item = self.create_line(
                self.plotCoords([(xm - w, ym, 0.0), (xm + w, ym, 0.0)]),
                tag="Orient",
                fill="Green",
            )
            self.tag_lower(item)
            paths.append(item)

            item = self.create_line(
                self.plotCoords([(xm, ym - w, 0.0), (xm, ym + w, 0.0)]),
                tag="Orient",
                fill="Green",
            )
            self.tag_lower(item)
            paths.append(item)

            # GCode position (cross)
            item = self.create_line(
                self.plotCoords([(x - w, y, 0.0), (x + w, y, 0.0)]),
                tag="Orient",
                fill="Red",
            )
            self.tag_lower(item)
            paths.append(item)

            item = self.create_line(
                self.plotCoords([(x, y - w, 0.0), (x, y + w, 0.0)]),
                tag="Orient",
                fill="Red",
            )
            self.tag_lower(item)
            paths.append(item)

            # Draw error if any
            try:
                err = self.gcode.orient.errors[i]
                item = self.create_oval(
                    self.plotCoords(
                        [(xm - err, ym - err, 0.0), (xm + err, ym + err, 0.0)]
                    ),
                    tag="Orient",
                    outline="Red",
                )
                self.tag_lower(item)
                paths.append(item)

                err = self.gcode.orient.errors[i]
                item = self.create_oval(
                    self.plotCoords([(x - err, y - err, 0.0),
                                     (x + err, y + err, 0.0)]),
                    tag="Orient",
                    outline="Red",
                )
                self.tag_lower(item)
                paths.append(item)
            except IndexError:
                pass

            # Connecting line
            item = self.create_line(
                self.plotCoords([(xm, ym, 0.0), (x, y, 0.0)]),
                tag="Orient",
                fill="Blue",
                dash=(1, 1),
            )
            self.tag_lower(item)
            paths.append(item)

            self.gcode.orient.addPath(paths)

        if self._orientSelected is not None:
            try:
                for item in self.gcode.orient.paths[self._orientSelected]:
                    self.itemconfig(item, width=2)
            except (IndexError, TclError):
                pass

    # ----------------------------------------------------------------------
    # Display probe
    # ----------------------------------------------------------------------
    def drawProbe(self):
        self.delete("Probe")
        if self._probe:
            self.delete(self._probe)
            self._probe = None
        if not self.draw_probe:
            return
        if self.view in (VIEW_XZ, VIEW_YZ):
            return

        # Draw probe grid
        probe = self.gcode.probe
        for x in bmath.frange(probe.xmin, probe.xmax + 0.00001, probe.xstep()):
            xyz = [(x, probe.ymin, 0.0), (x, probe.ymax, 0.0)]
            item = self.create_line(
                self.plotCoords(xyz), tag="Probe", fill="Yellow")
            self.tag_lower(item)

        for y in bmath.frange(probe.ymin, probe.ymax + 0.00001, probe.ystep()):
            xyz = [(probe.xmin, y, 0.0), (probe.xmax, y, 0.0)]
            item = self.create_line(
                self.plotCoords(xyz), tag="Probe", fill="Yellow")
            self.tag_lower(item)

        # Draw probe points
        for i, uv in enumerate(self.plotCoords(probe.points)):
            item = self.create_text(
                uv,
                text=f"{probe.points[i][2]:.{CNC.digits}f}",
                tag="Probe",
                justify=CENTER,
                fill=PROBE_TEXT_COLOR,
            )
            self.tag_lower(item)

        # Draw image map if numpy exists
        if (
            numpy is not None
            and probe.matrix
            and self.view in (VIEW_XY, VIEW_ISO1, VIEW_ISO2, VIEW_ISO3)
        ):
            array = numpy.array(list(reversed(probe.matrix)), numpy.float32)

            lw = array.min()
            hg = array.max()
            mx = max(abs(hg), abs(lw))
            # scale should be:
            #  -mx   .. 0 .. mx
            #  -127     0    127
            # -127 = light-blue
            #    0 = white
            #  127 = light-red
            dc = mx / 127.0  # step in colors
            if abs(dc) < 1e-8:
                return
            palette = []
            for x in bmath.frange(lw, hg + 1e-10, (hg - lw) / 255.0):
                i = int(math.floor(x / dc))
                j = i + i >> 1  # 1.5*i
                if i < 0:
                    palette.append(0xFF + j)
                    palette.append(0xFF + j)
                    palette.append(0xFF)
                elif i > 0:
                    palette.append(0xFF)
                    palette.append(0xFF - j)
                    palette.append(0xFF - j)
                else:
                    palette.append(0xFF)
                    palette.append(0xFF)
                    palette.append(0xFF)
            array = numpy.floor((array - lw) / (hg - lw) * 255)
            self._probeImage = Image.fromarray(
                array.astype(numpy.int16)).convert("L")
            self._probeImage.putpalette(palette)

            # Add transparency for a possible composite operation latter on ISO*
            self._probeImage = self._probeImage.convert("RGBA")

            x, y = self._projectProbeImage()

            self._probe = self.create_image(
                x, y, image=self._probeTkImage, anchor="sw")
            self.tag_lower(self._probe)

    # ----------------------------------------------------------------------
    # Create the tkimage for the current projection
    # ----------------------------------------------------------------------
    def _projectProbeImage(self):
        probe = self.gcode.probe
        size = (
            int((probe.xmax - probe.xmin + probe._xstep) * self.zoom),
            int((probe.ymax - probe.ymin + probe._ystep) * self.zoom),
        )
        marginx = int(probe._xstep / 2.0 * self.zoom)
        marginy = int(probe._ystep / 2.0 * self.zoom)
        crop = (marginx, marginy, size[0] - marginx, size[1] - marginy)

        image = self._probeImage.resize((size), resample=RESAMPLE).crop(crop)

        if self.view in (VIEW_ISO1, VIEW_ISO2, VIEW_ISO3):
            w, h = image.size
            size2 = (int(S60 * (w + h)), int(C60 * (w + h)))

            if self.view == VIEW_ISO1:
                transform = (
                    0.5 / S60, 0.5 / C60, -h / 2, -0.5 / S60, 0.5 / C60, h / 2)
                xy = self.plotCoords(
                    [(probe.xmin, probe.ymin, 0.0),
                     (probe.xmax, probe.ymin, 0.0)]
                )
                x = xy[0][0]
                y = xy[1][1]

            elif self.view == VIEW_ISO2:
                transform = (
                    0.5 / S60, -0.5 / C60, w / 2, 0.5 / S60, 0.5 / C60, -w / 2)

                xy = self.plotCoords(
                    [(probe.xmin, probe.ymax, 0.0),
                     (probe.xmin, probe.ymin, 0.0)]
                )
                x = xy[0][0]
                y = xy[1][1]
            else:
                transform = (
                    -0.5 / S60,
                    -0.5 / C60,
                    w + h / 2,
                    0.5 / S60,
                    -0.5 / C60,
                    h / 2,
                )
                xy = self.plotCoords(
                    [(probe.xmax, probe.ymax, 0.0),
                     (probe.xmin, probe.ymax, 0.0)]
                )
                x = xy[0][0]
                y = xy[1][1]

            affine = image.transform(
                size2, Image.AFFINE, transform, resample=RESAMPLE)
            # Super impose a white image
            white = Image.new("RGBA", affine.size, (255,) * 4)
            # compose the two images affine and white with mask the affine
            image = Image.composite(affine, white, affine)
            del white

        else:
            x, y = self.plotCoords([(probe.xmin, probe.ymin, 0.0)])[0]

        self._probeTkImage = ImageTk.PhotoImage(image)
        return x, y

    # ----------------------------------------------------------------------
    # Create paths for the whole gcode file
    # ----------------------------------------------------------------------
    def createPaths(self):
        if not self.draw_paths:
            for block in self.gcode.blocks:
                block.resetPath()
            return

        try:
            n = 1
            startTime = before = time.time()
            self.cnc.resetAllMargins()
            drawG = self.draw_rapid or self.draw_paths or self.draw_margin
            for i, block in enumerate(self.gcode.blocks):
                start = True  # start location found
                block.resetPath()

                # Draw block
                for j, line in enumerate(block):
                    n -= 1
                    if n == 0:
                        if time.time() - startTime > DRAW_TIME:
                            raise AlarmException()
                        # Force a periodic update since this loop can take time
                        if time.time() - before > 1.0:
                            self.update()
                            before = time.time()
                        n = 1000
                    try:
                        cmd = self.gcode.evaluate(
                            CNC.compileLine(line), self.app)
                        if isinstance(cmd, tuple):
                            cmd = None
                        else:
                            cmd = CNC.breakLine(cmd)
                    except AlarmException:
                        raise
                    except Exception:
                        sys.stderr.write(
                            _(">>> ERROR: {}\n").format(str(sys.exc_info()[1]))
                        )
                        sys.stderr.write(_("     line: {}\n").format(line))
                        cmd = None
                    if cmd is None or not drawG:
                        block.addPath(None)
                    else:
                        path = self.drawPath(block, cmd)
                        self._items[path] = i, j
                        block.addPath(path)
                        if start and self.cnc.gcode in (1, 2, 3):
                            # Mark as start the first non-rapid motion
                            block.startPath(self.cnc.x, self.cnc.y, self.cnc.z)
                            start = False
                block.endPath(self.cnc.x, self.cnc.y, self.cnc.z)
        except AlarmException:
            self.status("Rendering takes TOO Long. Interrupted...")

    # ----------------------------------------------------------------------
    # Create path for one g command
    # ----------------------------------------------------------------------
    def drawPath(self, block, cmds):
        self.cnc.motionStart(cmds)
        xyz = self.cnc.motionPath()
        self.cnc.motionEnd()
        if xyz:
            self.cnc.pathLength(block, xyz)
            if self.cnc.gcode in (1, 2, 3):
                block.pathMargins(xyz)
                self.cnc.pathMargins(block)
            
            flags = 0

            if block.enable:
                flags |= FLAG_ENABLED

                if self.cnc.gcode == 0 and self.draw_rapid:
                    xyz[0] = self._last
                self._last = xyz[-1]

            else:
                if self.cnc.gcode == 0:
                    return None                

            if block.color:
                fill = block.color
                
            else:
                fill = ENABLE_COLOR

            if self.cnc.gcode == 0:
                if self.draw_rapid:
                    return self.create_line(xyz, (255, 0, 0), 0.5, flags)
                
            elif self.draw_paths:
                return self.create_line(xyz, (numpy.array(self.winfo_rgb(fill)) * 255. / 65535.).astype(int), 1, flags)
            
        return None

    # ----------------------------------------------------------------------
    # Return plotting coordinates for a 3d xyz path
    #
    # NOTE: Use the tkinter._flatten() to pass to self.coords() function
    # ----------------------------------------------------------------------
    def plotCoords(self, xyz):
        coords = None
        if self.view == VIEW_XY:
            coords = [(p[0] * self.zoom, -p[1] * self.zoom) for p in xyz]
        elif self.view == VIEW_XZ:
            coords = [(p[0] * self.zoom, -p[2] * self.zoom) for p in xyz]
        elif self.view == VIEW_YZ:
            coords = [(p[1] * self.zoom, -p[2] * self.zoom) for p in xyz]
        elif self.view == VIEW_ISO1:
            coords = [
                (
                    (p[0] * S60 + p[1] * S60) * self.zoom,
                    (+p[0] * C60 - p[1] * C60 - p[2]) * self.zoom,
                )
                for p in xyz
            ]
        elif self.view == VIEW_ISO2:
            coords = [
                (
                    (p[0] * S60 - p[1] * S60) * self.zoom,
                    (-p[0] * C60 - p[1] * C60 - p[2]) * self.zoom,
                )
                for p in xyz
            ]
        elif self.view == VIEW_ISO3:
            coords = [
                (
                    (-p[0] * S60 - p[1] * S60) * self.zoom,
                    (-p[0] * C60 + p[1] * C60 - p[2]) * self.zoom,
                )
                for p in xyz
            ]
        # Check limits
        for i, (x, y) in enumerate(coords):
            if abs(x) > MAXDIST or abs(y) > MAXDIST:
                if x < -MAXDIST:
                    x = -MAXDIST
                elif x > MAXDIST:
                    x = MAXDIST
                if y < -MAXDIST:
                    y = -MAXDIST
                elif y > MAXDIST:
                    y = MAXDIST
                coords[i] = (x, y)
        return coords

    # ----------------------------------------------------------------------
    # Canvas to real coordinates
    # ----------------------------------------------------------------------
    def canvas2xyz(self, i, j):
        # Calculate the coords mapped from -1.0 to +1.0
        x = -1.0 + 2 * i / self.winfo_width()
        y = +1.0 - 2 * j / self.winfo_height()
        z = 0

        # Calculate xyz coords
        MVP = self.PMatrix * self.MVMatrix

        # Calculate the inverse of MVP
        MVPinv = inverse(MVP)

        # 3D Coords
        coords_3d = MVPinv * vec4(x, y, z, 1)

        return coords_3d.x, coords_3d.y, coords_3d.z


# =============================================================================
# Canvas Frame with toolbar
# =============================================================================
class CanvasFrame(Frame):
    def __init__(self, master, app, *kw, **kwargs):
        Frame.__init__(self, master, *kw, **kwargs)
        self.app = app

        self.draw_axes = BooleanVar()
        self.draw_grid = BooleanVar()
        self.draw_margin = BooleanVar()
        self.draw_probe = BooleanVar()
        self.draw_paths = BooleanVar()
        self.draw_rapid = BooleanVar()
        self.draw_workarea = BooleanVar()
        self.draw_camera = BooleanVar()
        self.view = StringVar()

        self.loadConfig()

        self.view.trace("w", self.viewChange)

        toolbar = Frame(self, relief=RAISED)
        toolbar.grid(row=0, column=0, columnspan=2, sticky=EW)

        # Ensure the Frame exists at the OS level before OpenGL initializes
        self.pack(side='top', fill='both', expand=True)
        self.update()

        self.canvas = CNCCanvas(self, app, takefocus=True, background="White")
        # OpenGL context
        print(f"self.canvas.winfo_id(): {self.canvas.winfo_id()}")
        self.canvas.grid(row=1, column=0, sticky=NSEW)
        """ sb = Scrollbar(self, orient=VERTICAL, command=self.canvas.yview)
        sb.grid(row=1, column=1, sticky=NS)
        self.canvas.config(yscrollcommand=sb.set)
        sb = Scrollbar(self, orient=HORIZONTAL, command=self.canvas.xview)
        sb.grid(row=2, column=0, sticky=EW)
        self.canvas.config(xscrollcommand=sb.set) """

        self.createCanvasToolbar(toolbar)

        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

    # ----------------------------------------------------------------------
    def addWidget(self, widget):
        self.app.widgets.append(widget)

    # ----------------------------------------------------------------------
    def loadConfig(self):
        global INSERT_COLOR, GANTRY_COLOR, MARGIN_COLOR, GRID_COLOR
        global BOX_SELECT, ENABLE_COLOR, DISABLE_COLOR, SELECT_COLOR
        global SELECT2_COLOR, PROCESS_COLOR, MOVE_COLOR, RULER_COLOR
        global CAMERA_COLOR, PROBE_TEXT_COLOR, CANVAS_COLOR
        global DRAW_TIME

        self.draw_axes.set(bool(int(Utils.getBool("Canvas", "axes", True))))
        self.draw_grid.set(bool(int(Utils.getBool("Canvas", "grid", True))))
        self.draw_margin.set(bool(int(Utils.getBool("Canvas", "margin", True))))
        self.draw_paths.set(bool(int(Utils.getBool("Canvas", "paths", True))))
        self.draw_rapid.set(bool(int(Utils.getBool("Canvas", "rapid", True))))
        self.draw_workarea.set(
            bool(int(Utils.getBool("Canvas", "workarea", True))))

        self.view.set(Utils.getStr("Canvas", "view", VIEWS[0]))

        DRAW_TIME = Utils.getInt("Canvas", "drawtime", DRAW_TIME)

        INSERT_COLOR = Utils.getStr("Color", "canvas.insert", INSERT_COLOR)
        GANTRY_COLOR = Utils.getStr("Color", "canvas.gantry", GANTRY_COLOR)
        MARGIN_COLOR = Utils.getStr("Color", "canvas.margin", MARGIN_COLOR)
        GRID_COLOR = Utils.getStr("Color", "canvas.grid", GRID_COLOR)
        BOX_SELECT = Utils.getStr("Color", "canvas.selectbox", BOX_SELECT)
        ENABLE_COLOR = Utils.getStr("Color", "canvas.enable", ENABLE_COLOR)
        DISABLE_COLOR = Utils.getStr("Color", "canvas.disable", DISABLE_COLOR)
        SELECT_COLOR = Utils.getStr("Color", "canvas.select", SELECT_COLOR)
        SELECT2_COLOR = Utils.getStr("Color", "canvas.select2", SELECT2_COLOR)
        PROCESS_COLOR = Utils.getStr("Color", "canvas.process", PROCESS_COLOR)
        MOVE_COLOR = Utils.getStr("Color", "canvas.move", MOVE_COLOR)
        RULER_COLOR = Utils.getStr("Color", "canvas.ruler", RULER_COLOR)
        CAMERA_COLOR = Utils.getStr("Color", "canvas.camera", CAMERA_COLOR)
        PROBE_TEXT_COLOR = Utils.getStr(
            "Color", "canvas.probetext", PROBE_TEXT_COLOR)
        CANVAS_COLOR = Utils.getStr("Color", "canvas.background", CANVAS_COLOR)

    # ----------------------------------------------------------------------
    def saveConfig(self):
        Utils.setInt("Canvas", "drawtime", DRAW_TIME)
        Utils.setStr("Canvas", "view", self.view.get())
        Utils.setBool("Canvas", "axes", self.draw_axes.get())
        Utils.setBool("Canvas", "grid", self.draw_grid.get())
        Utils.setBool("Canvas", "margin", self.draw_margin.get())
        Utils.setBool("Canvas", "probe", self.draw_probe.get())
        Utils.setBool("Canvas", "paths", self.draw_paths.get())
        Utils.setBool("Canvas", "rapid", self.draw_rapid.get())
        Utils.setBool("Canvas", "workarea", self.draw_workarea.get())

    # ----------------------------------------------------------------------
    # Canvas toolbar FIXME XXX should be moved to CNCCanvas
    # ----------------------------------------------------------------------
    def createCanvasToolbar(self, toolbar):
        b = OptionMenu(toolbar, self.view, *VIEWS)
        b.config(padx=0, pady=1)
        b.unbind("F10")
        b.pack(side=LEFT)
        tkExtra.Balloon.set(b, _("Change viewing angle"))

        b = Button(
            toolbar, image=Utils.icons["zoom_in"],
            command=self.canvas.menuZoomIn
        )
        tkExtra.Balloon.set(b, _("Zoom In [Ctrl-=]"))
        b.pack(side=LEFT)

        b = Button(
            toolbar, image=Utils.icons["zoom_out"],
            command=self.canvas.menuZoomOut
        )
        tkExtra.Balloon.set(b, _("Zoom Out [Ctrl--]"))
        b.pack(side=LEFT)

        b = Button(
            toolbar, image=Utils.icons["zoom_on"],
            command=self.canvas.fit2Screen
        )
        tkExtra.Balloon.set(b, _("Fit to screen [F]"))
        b.pack(side=LEFT)

        Label(toolbar, text=_("Tool:"),
              image=Utils.icons["sep"], compound=LEFT).pack(
            side=LEFT, padx=2
        )
        # -----
        # Tools
        # -----
        b = Radiobutton(
            toolbar,
            image=Utils.icons["select"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_SELECT,
            command=self.canvas.setActionSelect,
        )
        tkExtra.Balloon.set(b, _("Select tool [S]"))
        self.addWidget(b)
        b.pack(side=LEFT)

        b = Radiobutton(
            toolbar,
            image=Utils.icons["pan"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_PAN,
            command=self.canvas.setActionPan,
        )
        tkExtra.Balloon.set(b, _("Pan viewport [X]"))
        b.pack(side=LEFT)

        b = Radiobutton(
            toolbar,
            image=Utils.icons["ruler"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_RULER,
            command=self.canvas.setActionRuler,
        )
        tkExtra.Balloon.set(b, _("Ruler [R]"))
        b.pack(side=LEFT)

        # -----------
        # Draw flags
        # -----------
        Label(toolbar, text=_("Draw:"), image=Utils.icons["sep"],
              compound=LEFT).pack(
            side=LEFT, padx=2
        )

        b = Checkbutton(
            toolbar,
            image=Utils.icons["axes"],
            indicatoron=False,
            variable=self.draw_axes,
            command=self.drawAxes,
        )
        tkExtra.Balloon.set(b, _("Toggle display of axes"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["grid"],
            indicatoron=False,
            variable=self.draw_grid,
            command=self.drawGrid,
        )
        tkExtra.Balloon.set(b, _("Toggle display of grid lines"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["margins"],
            indicatoron=False,
            variable=self.draw_margin,
            command=self.drawMargin,
        )
        tkExtra.Balloon.set(b, _("Toggle display of margins"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            text="P",
            image=Utils.icons["measure"],
            indicatoron=False,
            variable=self.draw_probe,
            command=self.drawProbe,
        )
        tkExtra.Balloon.set(b, _("Toggle display of probe"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["endmill"],
            indicatoron=False,
            variable=self.draw_paths,
            command=self.toggleDrawFlag,
        )
        tkExtra.Balloon.set(b, _("Toggle display of paths (G1,G2,G3)"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["rapid"],
            indicatoron=False,
            variable=self.draw_rapid,
            command=self.toggleDrawFlag,
        )
        tkExtra.Balloon.set(b, _("Toggle display of rapid motion (G0)"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["workspace"],
            indicatoron=False,
            variable=self.draw_workarea,
            command=self.drawWorkarea,
        )
        tkExtra.Balloon.set(b, _("Toggle display of workarea"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["camera"],
            indicatoron=False,
            variable=self.draw_camera,
            command=self.drawCamera,
        )
        tkExtra.Balloon.set(b, _("Toggle display of camera"))
        b.pack(side=LEFT)
        if Camera.cv is None:
            b.config(state=DISABLED)

        b = Button(toolbar, image=Utils.icons["refresh"],
                   command=self.viewChange)
        tkExtra.Balloon.set(b, _("Redraw display [Ctrl-R]"))
        b.pack(side=LEFT)

        # -----------
        self.drawTime = tkExtra.Combobox(
            toolbar, width=3, background="White", command=self.drawTimeChange
        )
        tkExtra.Balloon.set(self.drawTime, _("Draw timeout in seconds"))
        self.drawTime.fill(
            ["inf", "1", "2", "3", "5", "10", "20", "30", "60", "120"])
        self.drawTime.set(DRAW_TIME)
        self.drawTime.pack(side=RIGHT)
        Label(toolbar, text=_("Timeout:")).pack(side=RIGHT)

    # ----------------------------------------------------------------------
    def redraw(self, event=None):
        self.canvas.reset()
        self.event_generate("<<ViewChange>>")

    # ----------------------------------------------------------------------
    def viewChange(self, a=None, b=None, c=None):
        # TODO: Change the view without fitting the screen. Show the current area instead
        view = VIEWS.index(self.view.get())

        self.canvas.MVMatrix = mat4x4(self.canvas.MVMatrix)

        if view == 0:
            self.canvas.MVMatrix = lookAt(
                vec3(0, 0, 1),
                vec3(0, 0, 0),
                vec3(0, 1, 0))
        elif view == 1:
            self.canvas.MVMatrix = lookAt(
                vec3(0, -1, 0),
                vec3(0, 0, 0),
                vec3(0, 0, 1))
        elif view == 2:
            self.canvas.MVMatrix = lookAt(
                vec3(1, 0, 0),
                vec3(0, 0, 0),
                vec3(0, 0, 1))
        elif view == 3:
            self.canvas.MVMatrix = lookAt(
                vec3(1, -1, 1),
                vec3(0, 0, 0),
                vec3(0, 0, 1))
        elif view == 4:
            self.canvas.MVMatrix = lookAt(
                vec3(-1, -1, 1),
                vec3(0, 0, 0),
                vec3(0, 0, 1))
        elif view == 5:
            self.canvas.MVMatrix = lookAt(
                vec3(-1, 1, 1),
                vec3(0, 0, 0),
                vec3(0, 0, 1))
        
        #self.event_generate("<<ViewChange>>")
        self.canvas.fit2Screen()

    # ----------------------------------------------------------------------
    def viewXY(self, event=None):
        self.view.set(VIEWS[VIEW_XY])

    # ----------------------------------------------------------------------
    def viewXZ(self, event=None):
        self.view.set(VIEWS[VIEW_XZ])

    # ----------------------------------------------------------------------
    def viewYZ(self, event=None):
        self.view.set(VIEWS[VIEW_YZ])

    # ----------------------------------------------------------------------
    def viewISO1(self, event=None):
        self.view.set(VIEWS[VIEW_ISO1])

    # ----------------------------------------------------------------------
    def viewISO2(self, event=None):
        self.view.set(VIEWS[VIEW_ISO2])

    # ----------------------------------------------------------------------
    def viewISO3(self, event=None):
        self.view.set(VIEWS[VIEW_ISO3])

    # ----------------------------------------------------------------------
    def toggleDrawFlag(self):
        self.canvas.draw_axes = self.draw_axes.get()
        self.canvas.draw_grid = self.draw_grid.get()
        self.canvas.draw_margin = self.draw_margin.get()
        self.canvas.draw_probe = self.draw_probe.get()
        self.canvas.draw_paths = self.draw_paths.get()
        self.canvas.draw_rapid = self.draw_rapid.get()
        self.canvas.draw_workarea = self.draw_workarea.get()
        self.event_generate("<<ViewChange>>")

    # ----------------------------------------------------------------------
    def drawAxes(self, value=None):
        if value is not None:
            self.draw_axes.set(value)
        self.canvas.draw_axes = self.draw_axes.get()
        self.canvas.createAxes()
        self.after('idle', self.canvas.draw)

    # ----------------------------------------------------------------------
    def drawGrid(self, value=None):
        if value is not None:
            self.draw_grid.set(value)
        self.canvas.draw_grid = self.draw_grid.get()
        self.canvas.updateGrid()

    # ----------------------------------------------------------------------
    def drawMargin(self, value=None):
        if value is not None:
            self.draw_margin.set(value)
        self.canvas.draw_margin = self.draw_margin.get()
        self.canvas.updateMargin()

    # ----------------------------------------------------------------------
    def drawProbe(self, value=None):
        if value is not None:
            self.draw_probe.set(value)
        self.canvas.draw_probe = self.draw_probe.get()
        self.canvas.drawProbe()

    # ----------------------------------------------------------------------
    def drawWorkarea(self, value=None):
        if value is not None:
            self.draw_workarea.set(value)
        self.canvas.draw_workarea = self.draw_workarea.get()
        self.canvas.updateWorkArea()

    # ----------------------------------------------------------------------
    def drawCamera(self, value=None):
        if value is not None:
            self.draw_camera.set(value)
        if self.draw_camera.get():
            self.canvas.cameraOn()
        else:
            self.canvas.cameraOff()

    # ----------------------------------------------------------------------
    def drawTimeChange(self):
        global DRAW_TIME
        try:
            DRAW_TIME = int(self.drawTime.get())
        except ValueError:
            DRAW_TIME = 5 * 60
        self.viewChange()