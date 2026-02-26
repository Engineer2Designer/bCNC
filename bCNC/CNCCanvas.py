# $Id: CNCCanvas.py,v 1.7 2014/10/15 15:04:06 bnv Exp $
#
# Author:       vvlachoudis@gmail.com
# Date: 24-Aug-2014

import math
import time
import sys
from numpy import deg2rad
from tkinter_gl import GLCanvas

import OpenGL
if sys.platform == 'linux':
    # PyOpenGL is broken with wayland:
    OpenGL.setPlatform('x11')

try:
    import cv2 as cv
except ImportError:
    cv = None

from OpenGL.GL import *
from ctypes import c_void_p
from pyglm.glm import mat4x4, mat3x3, ortho, identity, value_ptr, inverse, translate, rotate, vec2, vec3, vec4, inverse, normalize, lookAt, dot, cross, distance, length2
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
from CNC import CNC, Probe

# Probe mapping we need PIL and numpy
try:
    from PIL import Image, ImageTk, ImageFont, ImageDraw
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

MOVE_COLOR = "DarkCyan"
RULER_COLOR = "Green"
PROBE_TEXT_COLOR = "Green"

INFO_COLOR = "Gold"

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
AXIS_LENGTH = 100 # Coord system axis length in pixels

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
    def rgb8(self, colorName):
        return (numpy.array(self.winfo_rgb(colorName)) * 255. / 65535.).astype(int)

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
        self.bind("<ButtonRelease-2>", self.midRelease)
        self.bind("<Button-4>", self.mouseZoomIn)
        self.bind("<Button-5>", self.mouseZoomOut)
        self.bind("<MouseWheel>", self.wheel)
        self.bind("<Button-3>", self.rightClick)
        self.bind("<B3-Motion>", self.rotate)
        self.bind("<ButtonRelease-3>", self.rightRelease)

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
        self._x = self._y = 0
        self._xp = self._yp = 0
        self.action = ACTION_SELECT
        self._mouseAction = None
        self._vector = None
        self._lastActive = None
        self._lastGantry = None
        self._gantryLocation = vec3(0, 0, 0)
        self._drawRequested = False

        self._probeImage = None
        self._probeTkImage = None
        self._probe = None
        self.probeMaxZ = 10
        self.probeMinZ = -10
        self.probeMaxHeight = 10

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
        self.cameraLocation = vec2(0., 0.)
        self._cameraAfter = None  # Camera anchor location "" for gantry
        self._showCamera = False

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
        self.pathLines = {}
        self.orientLines = {}
        self.probeLines = {}
        self.vectorLines = {}
        
        self.infoVertices = numpy.array([], dtype=numpy.float32)
        self.pathVertices = numpy.array([], dtype=numpy.float32)
         # Grid
        self.gridVertices = numpy.array([], dtype=numpy.float32)
        # Selection Rectangle
        self.SelectionRectVertices = numpy.array([], dtype=numpy.float32)
        
        self.pathArrows = {}
        self.infoArrows = {}
        
        self._modelCenter = vec3(0, 0, 0)
        self._modelSize = 100.0
        # Text items
        self._text_id = 1
        self.text = {} # text_id[location, text value, color]
        self.probeText = {}
        # Background gradiend colors
        self.bgColorUp = vec3(0.175, 0.215, 0.392)
        self.bgColorDn = vec3(0.4, 0.4, 0.6)
        
        self.reset()
        self.initGL()

        # Data of Texture atlas for text rendering
        self.charOffsetAndWidth = []
        self.create_char_texture("./bCNC/opengl/DejaVuSans.ttf", 12)

        self.createAxes(AXIS_LENGTH)
        self.createGantry()

        self.initPosition()
    
    def get_camera_image(self):
        if (self.camera.image is None) or (cv is None):
            return None
        
        tex = cv.flip(cv.cvtColor(self.camera.image, cv.COLOR_BGR2RGBA), 0)
    
        return tex

    def create_char_texture(self, font_name, font_size):
        font = ImageFont.truetype(font_name, font_size)

        # Get font metrics (ascent = top above baseline, descent = below baseline)
        ascent, descent = font.getmetrics()

        # Full safe height for drawing
        self.textHeight = ascent + descent

        # Get the width and offset of each char
        offset = 0
        for ch in range(128):
            width = font.getlength(chr(ch))
            self.charOffsetAndWidth.append([offset, width])
            offset += width
        
        image = Image.new("RGBA", (int(offset), int(self.textHeight)), (0, 0, 0, 0)) # type: ignore
        
        # Create a drawing object
        draw = ImageDraw.Draw(image)

        # Create an image with all the ascii chars
        for ch in range(128):
            draw.text((self.charOffsetAndWidth[ch][0], 0), chr(ch), fill="white", font=font)
        
        image = image.transpose(Image.FLIP_TOP_BOTTOM)  # OpenGL expects the y-axis to be flipped

        self.charTextureAtlas = numpy.array(image)

        glBindTexture(GL_TEXTURE_2D, self.textTexture)

        # Set the texture parameters
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST)

        # Upload texture data to OpenGL
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, len(self.charTextureAtlas[0]), len(self.charTextureAtlas), 0, GL_RGBA, GL_UNSIGNED_BYTE, self.charTextureAtlas)

        # Generate Mipmap
        glGenerateMipmap(GL_TEXTURE_2D)
    
    def create_text(self, textDict, location, text, color):
        # Color is a tuple or numpy array of three 8bit integers
        textDict[self._text_id] = [location, text, color]

        id = self._text_id
        self._text_id += 1

        return id

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
        
        # ----- LINES PROGRAM ------
        # Vertex Shader code
        with open(openglFolder + "LinesVS.shd", "r") as file:
            LinesVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "LinesFS.shd", "r") as file:
            LinesFSCode = file.read()

        self.linesProgram = self.createProgram(LinesVSCode, LinesFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.pathVBO = glGenBuffers(1)
        self.marginsVBO = glGenBuffers(1)
        self.workAreaVBO = glGenBuffers(1)
        self.infoVBO = glGenBuffers(1)
        self.orientVBO = glGenBuffers(1)
        self.probeVBO = glGenBuffers(1)
        
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

        # ----- TEXT PROGRAM ------
        # Program to draw text
        # Vertex Shader code
        with open(openglFolder + "TextVS.shd", "r") as file:
            TextVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "TextFS.shd", "r") as file:
            TextFSCode = file.read()

        self.TextProgram = self.createProgram(TextVSCode, TextFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.TextVBO = glGenBuffers(1)
        self.AxesTextVBO = glGenBuffers(1)
        self.ProbeTextVBO = glGenBuffers(1)

        # ----- PROBE MAP PROGRAM ------
        # Program to draw text
        # Vertex Shader code
        with open(openglFolder + "ProbeMapVS.shd", "r") as file:
            ProbeMapVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "ProbeMapFS.shd", "r") as file:
            ProbeMapFSCode = file.read()

        self.ProbeMapProgram = self.createProgram(ProbeMapVSCode, ProbeMapFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.ProbeMapVBO = glGenBuffers(1)

        # ----- IMAGE PROGRAM ------
        # Program to draw images
        # Vertex Shader code
        with open(openglFolder + "ImageVS.shd", "r") as file:
            ImageVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "ImageFS.shd", "r") as file:
            ImageFSCode = file.read()

        self.ImageProgram = self.createProgram(ImageVSCode, ImageFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.CameraVBO = glGenBuffers(1)

        # Create textures
        self.textTexture = glGenTextures(1)
        self.cameraTexture = glGenTextures(1)

        # Fill the buffer of the camera rectangle, which is fixed
        glBindBuffer(GL_ARRAY_BUFFER, self.CameraVBO)
        CameraRectVertices = numpy.array([1., 2., 3., 1., 3., 4.], dtype=numpy.float32)

        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glBufferData(GL_ARRAY_BUFFER, size, CameraRectVertices, GL_STATIC_DRAW)
        
        # ----- ARROW PROGRAM ------
        # Program to draw arrows
        # Vertex Shader code
        with open(openglFolder + "ArrowVS.shd", "r") as file:
            ArrowVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "ArrowFS.shd", "r") as file:
            ArrowFSCode = file.read()

        self.ArrowProgram = self.createProgram(ArrowVSCode, ArrowFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.pathArrowsVBO = glGenBuffers(1)
        self.infoArrowsVBO = glGenBuffers(1)
        
        # ----- CROSSHAIR PROGRAM ------
        # Program to draw the Camera Crosshair
        # Vertex Shader code
        with open(openglFolder + "CrossHairVS.shd", "r") as file:
            CrossHairVSCode = file.read()

        # Fragment Shader code
        with open(openglFolder + "CrossHairFS.shd", "r") as file:
            CrossHairFSCode = file.read()

        self.CrossHairProgram = self.createProgram(CrossHairVSCode, CrossHairFSCode)
        
        # Create a Vertex Buffer Object (VBO)
        self.CrossHairVBO = glGenBuffers(1)

        # Fill the buffer of the crosshair, which is fixed
        glBindBuffer(GL_ARRAY_BUFFER, self.CrossHairVBO)
        CrossHairVertices = numpy.arange(1, 293, dtype=numpy.float32)
        glBufferData(GL_ARRAY_BUFFER, CrossHairVertices.nbytes, CrossHairVertices, GL_STATIC_DRAW)


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
        
    def create_line(self, lines, xyz, colorRGB, dashRatio, flags = FLAG_ENABLED):
        # xyz is an array of arrays of 3d coords
        lines[self._line_id] = [xyz, colorRGB, dashRatio, flags]
        
        id = self._line_id
        # Increment the line id for the next line
        self._line_id += 1
        
        return id
    
    def create_arrow(self, arrows, id, location, direction, width, height, colorRGB, flags = FLAG_ENABLED):
        arrows[id] = [location, direction, width, height, colorRGB, flags]
    
    def set_arrow(self, arrows, arrowsBuffer, linesVertices, lineId, position, width = 0, height = 0):
        """
        Add arrow to a line id from the numpy array linesVertices.
        Position can be 'none', 'first', 'last' or 'both'
        """

        if position == 'none':
            if (lineId + 0.1) in arrows:
                del arrows[lineId + 0.1]

            if (lineId + 0.2) in arrows:
                del arrows[lineId + 0.2]
        
        else:
            lines16 = numpy.reshape(linesVertices, (-1, 16))
            line16 = lines16[lines16[:, 0] == lineId]

            if len(line16) == 0:
                return
            
            if position == 'first' or position == 'both':
                p_tip = vec3(line16[0, 1:4])
                p_base = vec3(line16[0, 9:12])
                dir = p_tip - p_base
                colorValue = line16[0, 5]
                R = (int(colorValue) & 0xFF0000) >> 16
                G = (int(colorValue) & 0xFF00) >> 8
                B = int(colorValue) & 0xFF
                colorRGB = [R, G, B]
                flags = line16[0, 7]

                self.create_arrow(arrows, lineId + 0.1, p_tip, dir, width, height, colorRGB, flags)
            
            if position == 'last' or position == 'both':
                p_tip = vec3(line16[-1, 9:12])
                p_base = vec3(line16[-1, 1:4])
                dir = p_tip - p_base
                colorValue = line16[-1, 5]
                R = (int(colorValue) & 0xFF0000) >> 16
                G = (int(colorValue) & 0xFF00) >> 8
                B = int(colorValue) & 0xFF
                colorRGB = [R, G, B]
                flags = line16[-1, 7]

                self.create_arrow(arrows, lineId + 0.2, p_tip, dir, width, height, colorRGB, flags)
        
        self.update_arrows_buffer(arrowsBuffer, arrows)


    
    def create_oval(self, lines, xyz_bottomleft, xyz_topright, colorRGB, dashRatio, flags = FLAG_ENABLED):
        p_bl = vec3(xyz_bottomleft)
        p_tr = vec3(xyz_topright)
        center = (p_bl + p_tr) / 2.
        Rx = abs(p_tr.x - center.x)
        Ry = abs(p_tr.y - center.y)
        
        xyz = []
        
        for angle in range(0, 360, 5):
            xyz.append([center.x + Rx * numpy.cos(numpy.deg2rad(angle)),
                        center.y + Ry * numpy.sin(numpy.deg2rad(angle)),
                        center.z])
            xyz.append([center.x + Rx * numpy.cos(numpy.deg2rad(angle + 5)),
                        center.y + Ry * numpy.sin(numpy.deg2rad(angle + 5)),
                        center.z])
            
        
        return self.create_line(lines, xyz, colorRGB, dashRatio, flags)
    
    def update_lines_buffer(self, buffer, lines, updateModelDimensions = False):        
        # In order to be compatible with Pi 3, we are using GLSL 1.0. It doesn't allow constant parameters per line in the fragment shader. They are always
        # interpolated between vertices. Then, we must assign the parameter twice, once per vertex, with the same value
        vertexArray = []
        
        maxX = maxY = maxZ = -999999
        minX = minY = minZ = 999999
        
        for id, data in lines.items():
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
                
                if updateModelDimensions:
                    # TODO: Optimize this
                    maxX = max(max(maxX, xyz[i][0]), xyz[i+1][0])
                    maxY = max(max(maxY, xyz[i][1]), xyz[i+1][1])
                    maxZ = max(max(maxZ, xyz[i][2]), xyz[i+1][2])
                    minX = min(min(minX, xyz[i][0]), xyz[i+1][0])
                    minY = min(min(minY, xyz[i][1]), xyz[i+1][1])
                    minZ = min(min(minZ, xyz[i][2]), xyz[i+1][2])

        if updateModelDimensions:
            if len(lines) == 0:
                self._modelCenter = vec3(0, 0, 0)
                self._modelSize = 100
            else:
                self._modelCenter = vec3((maxX + minX) / 2, (maxY + minY) / 2, (maxZ + minZ) / 2)
                self._modelSize = math.sqrt(math.pow(maxX-minX, 2) + math.pow(maxY-minY, 2) + math.pow(maxZ-minZ, 2))
        
        vertices = numpy.array(vertexArray, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, buffer)
        glBufferData(GL_ARRAY_BUFFER, vertices.nbytes, vertices, GL_DYNAMIC_DRAW)

        glBindBuffer(GL_ARRAY_BUFFER, 0)  # Unbind the VBO

        return vertices
    
    def update_arrows_from_lines(self, arrows, arrowsBuffer, linesVertices):
        """
        Update arrow color and flags from lines
        """

        if len(arrows) == 0:
            return
        
        lines16 = numpy.reshape(linesVertices, (-1, 16))

        for arrowId in arrows:
            lineId = int(arrowId)
            line16 = lines16[lines16[:, 0] == lineId]
            if len(line16 > 0):
                line16 = line16[0]
                #arrows[id] = [location, direction, width, height, colorRGB, flags]

                # Copy color from line
                colorValue = line16[5]
                R = (int(colorValue) & 0xFF0000) >> 16
                G = (int(colorValue) & 0xFF00) >> 8
                B = int(colorValue) & 0xFF
                colorRGB = [R, G, B]
                arrows[arrowId][4] = colorRGB
                
                # Copy flags from line
                arrows[arrowId][5] = line16[7]
        
        self.update_arrows_buffer(arrowsBuffer, arrows)


    def update_arrows_buffer(self, buffer, arrows):        
        vertexArray = []
        
        for id, data in arrows.items():
            colorValue = (data[4][0] << 16) + (data[4][1] << 8) + data[4][2] # RGB
            
            vertexArray.extend([
                # Vertex 1
                id,
                1.,
                data[0][0], # location.x
                data[0][1], # location.y
                data[0][2], # location.z
                data[1][0], # direction.x
                data[1][1], # direction.y
                data[1][2], # direction.z
                data[2], # width
                data[3], # height
                colorValue,
                data[5], # flags
                # Vertex 2
                id,
                2.,
                data[0][0], # location.x
                data[0][1], # location.y
                data[0][2], # location.z
                data[1][0], # direction.x
                data[1][1], # direction.y
                data[1][2], # direction.z
                data[2], # width
                data[3], # height
                colorValue,
                data[5], # flags
                # Vertex 3
                id,
                3.,
                data[0][0], # location.x
                data[0][1], # location.y
                data[0][2], # location.z
                data[1][0], # direction.x
                data[1][1], # direction.y
                data[1][2], # direction.z
                data[2], # width
                data[3], # height
                colorValue,
                data[5], # flags
            ])
        
        vertices = numpy.array(vertexArray, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, buffer)
        glBufferData(GL_ARRAY_BUFFER, vertices.nbytes, vertices, GL_DYNAMIC_DRAW)

        glBindBuffer(GL_ARRAY_BUFFER, 0)  # Unbind the VBO

        return vertices
    
    def update_text_buffer(self, buffer, textDict: dict):
        char_data = []
        
        for id in textDict.keys():
            hOffset = 0

            location = textDict[id][0]
            text = textDict[id][1]
            color = textDict[id][2]
            colorValue = (color[0] << 16) + (color[1] << 8) + color[2] # RGB

            for ch in range(len(text)):
                # We define a quad as 2 triangles (6 vertices)
                char_data.extend([
                # Bottom left
                    id, # Text id
                    1, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                # Bottom left
                    id, # Text id
                    2, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                # Bottom left
                    id, # Text id
                    3, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                # Bottom left
                    id, # Text id
                    1, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                # Bottom left
                    id, # Text id
                    3, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                # Bottom left
                    id, # Text id
                    4, # Vertex index
                    location[0], # Location of the bottom left corner
                    location[1],
                    location[2],
                    hOffset,
                    self.charOffsetAndWidth[ord(text[ch])][0], # Char offset in texture atlas in pixels
                    self.charOffsetAndWidth[ord(text[ch])][1], # Char width in texture atlas in pixels
                    self.textHeight, #Char height in texture atlas
                    colorValue,
                ])

                hOffset += self.charOffsetAndWidth[ord(text[ch])][1]
            
        textVertices = numpy.array(char_data, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, buffer)
        glBufferData(GL_ARRAY_BUFFER, textVertices.nbytes, textVertices, GL_DYNAMIC_DRAW)

        glBindBuffer(GL_ARRAY_BUFFER, 0)  # Unbind the VBO

        return textVertices

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
        self.configure(cursor=mouseCursor(self.action))

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
        # TODO: #self.config(background="seashell")
        self.status(_("Move CNC gantry to mouse location"))

    # ----------------------------------------------------------------------
    def setActionWPOS(self, event=None):
        self.setAction(ACTION_WPOS)
        # TODO: # self.config(background="ivory")
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
        xy_w = self.canvas2WorldXY(vec2(x, y)) # self.image2Machine(x, y)
        
        if xy_w is not None:
            self.app.goto(xy_w.x, xy_w.y, 0)
        else:
            self.status(
                _("ERROR: Cannot set Gantry location with the current view (Too parallel to the XY plane)"))
        
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Set the work coordinates to mouse location
    # ----------------------------------------------------------------------
    def actionWPOS(self, x, y):
        xy_w = self.canvas2WorldXY(vec2(x, y)) # self.image2Machine(x, y)
        
        if xy_w is not None:
            self.app.mcontrol._wcsSet(xy_w.x, xy_w.y, 0)
        else:
            self.status(
                _("ERROR: Cannot set WPOS with the current view (Too parallel to the XY plane)"))
        
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Add an orientation marker at mouse location
    # ----------------------------------------------------------------------
    def actionAddOrient(self, x, y):
        cx, cy = self.snapPoint(x, y)
        
        # Proyect the canvas cx, cy point to the world xy plane
        uv = self.canvas2WorldXY(vec2(cx, cy))

        if uv is None:
            self.status(
                _("ERROR: Cannot set X-Y marker with the current view (Too parallel to the XY plane)"))
            return
        self._orientSelected = len(self.gcode.orient)
        self.gcode.orient.add(CNC.vars["wx"], CNC.vars["wy"], uv.x, uv.y)
        self.event_generate("<<OrientSelect>>", data=self._orientSelected)
        self.setAction(ACTION_SELECT)

        self.status(
                _("X-Y marker created."))

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
            i = event.x
            j = event.y
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
                        event.x - CLOSE_DISTANCE,
                        event.y - CLOSE_DISTANCE,
                        event.x + CLOSE_DISTANCE,
                        event.y + CLOSE_DISTANCE,
                        self.pathVertices
                    ):
                        if self.isSelected(item, self.pathVertices):
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
            self._vector = self.create_line(self.vectorLines,)
            """
            self._vector = self.create_line(
                (i, j, i, j), fill=fill, arrow=arrow)
            self._vx0, self._vy0, self._vz0 = self.canvas2xyz(i, j)
            """
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
            xy_w = self.canvas2WorldXY(vec2(event.x, event.y))
            if xy_w is not None:
                self.app.insertCommand(_("origin {:g} {:g} {:g}").format(xy_w.x, xy_w.y, 0),
                                   True)
            else:
                self.status(
                _("ERROR: Cannot set Origin with the current view (Too parallel to the XY plane)"))
            
            self.setActionSelect()

        elif self.action == ACTION_PAN:
            self.pan(event)

    def isSelected(self, lineId, lineVertices):


    def midClick(self, event):
        self._x = event.x
        self._y = event.y
    
    def rightClick(self, event):
        self._x = event.x
        self._y = event.y
    
    def rotate(self, event):
        if (self._x == event.x and self._y == event.y):
            return
        
        self.configure(cursor=mouseCursor(ACTION_ROTATE))

        RotAxis = normalize(vec4(event.y - self._y, event.x - self._x, 0, 0))
        
        RotAxis = inverse(self.MVMatrix) * RotAxis

        # Rotate about the Center of the screen
        rotationCenter = self.canvas2World(vec2(self.winfo_width() / 2., self.winfo_height() / 2.))

        self.MVMatrix = translate(self.MVMatrix, rotationCenter)

        self.MVMatrix = rotate(self.MVMatrix,
            0.01 * math.sqrt(pow(event.y - self._y, 2) + math.pow(event.x - self._x, 2)),
            vec3(RotAxis.x, RotAxis.y, RotAxis.z)) # type: ignore

        self.MVMatrix = translate(self.MVMatrix, -rotationCenter)
        
        self._x = event.x
        self._y = event.y
        
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
        
    def find_enclosed(self, x1, y1, x2, y2, lines):
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

        # Boolean mask for both endpoints inside
        mask = (
            (linesCanvasUnit[:, 0] >= xmin) & (linesCanvasUnit[:, 0] <= xmax) &
            (linesCanvasUnit[:, 1] >= ymin) & (linesCanvasUnit[:, 1] <= ymax) &
            (linesCanvasUnit[:, 2] >= xmin) & (linesCanvasUnit[:, 2] <= xmax) &
            (linesCanvasUnit[:, 3] >= ymin) & (linesCanvasUnit[:, 3] <= ymax)
        )

        lines_16 = numpy.reshape(lines, (-1, 16))[:, 0]
        
        return numpy.unique(lines_16[mask]).tolist() 
    
    def find_closest(self, x, y, lines, tolerance, returnIndex = False):
        # Unit coordinates of the selection area boundaries
        xy = self.canvas2Unit(vec2(x, y))

        # tolerance in unit distance
        unitTolX = tolerance / self.winfo_width() * 2
        unitTolY = tolerance / self.winfo_height() * 2
        
        xmin = xy.x - unitTolX
        xmax = xy.x + unitTolX
        ymin = xy.y - unitTolY
        ymax = xy.y + unitTolY
        
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
        
        # TODO: Return the closest one, not the first in the list...

        # If returnIndex is True, return the index of the closest line in the lines array, instead of the closest line ID
        if returnIndex:
            indices = numpy.arange(lines.size / 16)
            selectedIndices = indices[intersects].tolist()

            if len(selectedIndices) == 0:
                return None
            else:
                return selectedIndices[0]
            
        else:
            # Get the ids of the overlapped lines (id is the 1st parameter of the lines array)
            lineIds = lines.reshape((-1, 16))[:, 0]
            
            selectedIds = numpy.unique(lineIds[intersects]).tolist()
            
            if len(selectedIds) == 0:
                return []
            else:
                return [selectedIds[0]]
    
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
                            self._x,
                            self._y,
                            event.x,
                            event.y,
                            self.pathVertices
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
                            self.pathVertices
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
                        event.x,
                        event.y,
                        self.pathVertices,
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
            self.midRelease(event)

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

    def get_ends_and_center(self, lines, id):
        # lines is an array with lines vertex data as self.pathLines
        
        # Reshape to have one line per row. Each row has the info of the 2 vertices (location, ...)
        lines16 = numpy.reshape(lines, (-1, 16))

        # Filter the lines with id. If there is more than one, it is an arc composed by multiple lines
        line16 = lines16[lines16[:, 0] == id]

        if len(line16) == 1: # Just one row. We picked on a line
            return vec3(line16[0, 1:4]), vec3(line16[0, 9:12]), None
        
        else: # Multiple rows. We picked on an arc. We return the first point of the first line and the last point of the last line
            p_start = vec3(line16[0, 1:4])
            p_end = vec3(line16[-1, 9:12])
            
            # If it's a closed arc (a circle), pick the starting point of the last line, instead of the end point
            if distance(p_start, p_end) == 0.:
                p_end = vec3(line16[-1, 1:4])
            
            numlines = len(line16)
            p_mid = vec3(line16[int(numpy.ceil(numlines / 2.)), 1:4])
            
            # Compute the arc center
            SM = p_mid - p_start
            SE = p_end - p_start

            cross_prod = cross(SM, SE)
            denom = 2.0 * length2(cross_prod)

            if denom == 0:
                p_center = None # Points are collinear
            else:
                term1 = cross(cross_prod, SM) * length2(SE)
                term2 = cross(SE, cross_prod) * length2(SM)

                p_center = p_start + (term1 + term2) / denom
                
            return p_start, p_end, p_center

    # ----------------------------------------------------------------------
    # Snap to the closest point if any
    # ----------------------------------------------------------------------
    def snapPoint(self, cx, cy):
        xs, ys = None, None

        item = self.find_closest(cx, cy, self.pathVertices, CLOSE_DISTANCE)

        if len(item) == 0:
            return cx, cy
        
        # Get the ends of the closest line, in canvas coordinates
        start, end, center = self.get_ends_and_center(self.pathVertices, item)

        start = self.world2Canvas(start)
        end = self.world2Canvas(end)

        dist_start = distance(vec2(cx, cy), start)
        dist_end = distance(vec2(cx, cy), end)

        if dist_start < dist_end and dist_start < CLOSE_DISTANCE:
            return start.x, start.y
        elif dist_end < dist_start and dist_end < CLOSE_DISTANCE:
            return end.x, end.y
        elif center is not None: # We clicked on an arc, far from the ends. Return the center point
            center = self.world2Canvas(center)
            #dist_center = distance(vec2(cx, cy), center)
            return center.x, center.y
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

    def closest_points_between_lines(self, P1, P2, Q1, Q2, eps=1e-9):
        """
        Compute closest points between two infinite 3D lines.

        Line 1: P1 + t*(P2-P1)
        Line 2: Q1 + u*(Q2-Q1)

        Returns:
            C1 : closest point on line 1
            C2 : closest point on line 2
            distance : minimum distance between lines
            intersect : True if lines intersect (within tolerance)
        """

        r = P2 - P1
        s = Q2 - Q1
        w0 = P1 - Q1

        a = dot(r, r)
        b = dot(r, s)
        c = dot(s, s)
        d = dot(r, w0)
        e = dot(s, w0)

        denom = a * c - b * b

        # If denom is zero, lines are parallel
        if abs(denom) < eps:
            # choose arbitrary t = 0
            t = 0.0
            u = e / c if c > eps else 0.0
        else:
            t = (b * e - c * d) / denom
            u = (a * e - b * d) / denom

        C1 = P1 + t * r
        C2 = Q1 + u * s

        dist = distance(C1, C2)
        intersect = dist < eps

        return C1, C2, dist, intersect

    def blue2red(self, v: float, vmin: float, vmax: float) -> vec3:
        """
        Return an interpolated RGB tuple, based on the value v between vmin and vmax
        v==vmin -> blue
        v==vmax -> red
        """
        if vmax <= vmin or v < vmin or v > vmax:
            return vec3(0, 0, 0)  # fallback
    
        t = (v - vmin) / (vmax - vmin)
        t = max(0, min(1, t))

        R = int(255 * t)
        G = 0
        B = int(255 * (1 - t))

        return vec3(R, G, B)

    # ----------------------------------------------------------------------
    def pan(self, event):
        if self._mouseAction != ACTION_PAN:
            self.configure(cursor=mouseCursor(ACTION_PAN))
            self._mouseAction = ACTION_PAN
            
        self.pan_delta(event.x - self._x, event.y - self._y)
        
        self._x = event.x
        self._y = event.y

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
    def midRelease(self, event):
        # If there was no pan (just mid-click), and the user clicked on a path, 
        # change the rotation center to the closest point of that line to the point where the user clicked
        if self._mouseAction != ACTION_PAN:
            lineIndex = self.find_closest(self._x, self._y, self.pathVertices, CLOSE_DISTANCE, True)
            
            if lineIndex is not None:
                line = self.pathVertices.reshape((-1, 16))[int(lineIndex)]
                lineStart = vec3(line[1:4])
                lineEnd = vec3(line[9:12])

                MVPinv = inverse(self.PMatrix * self.MVMatrix)

                pickPoint = self.canvas2Unit(vec2(event.x, event.y))

                # pickLine is a line perpendicular to the screen
                pickLineStart =  vec3(MVPinv * vec4(pickPoint.x, pickPoint.y, 0, 1))
                pickLineEnd = vec3(MVPinv * vec4(pickPoint.x, pickPoint.y, -1, 1))

                # If pickLine does not exactly intersect line, we get 2 points:
                # C1: closest point at pickLine
                # C2: closest point at line
                C1, C2, dist, intersect = self.closest_points_between_lines(pickLineStart, pickLineEnd, lineStart, lineEnd)

                # Translate the MV Matrix, so that the clicked point moves to the screen center
                RS = mat3x3(self.MVMatrix)
                new_translation = -RS * C2
                self.MVMatrix[3] = vec4(new_translation, 1)

                self.queueDraw()

        self._mouseAction = None
        self.configure(cursor=mouseCursor(self.action))

    def rightRelease(self, event):
        self.configure(cursor=mouseCursor(self.action))

    # ----------------------------------------------------------------------
    def panLeft(self, event=None):
        self.pan_delta(15, 0) # 15 pixels, as in the original canvas

    def panRight(self, event=None):
        self.pan_delta(-15, 0)

    def panUp(self, event=None):
        self.pan_delta(0, 15)

    def panDown(self, event=None):
        self.pan_delta(0, -15)

    def canvas2Unit(self, coords : vec2) -> vec2:
        # Map screen pixel coordinates to opengl screen coords [-1.0 -> 1.0]
        # In OpenGL, y goes positive upwards
        width = self.winfo_width()
        height = self.winfo_height()
        
        return vec2(
            coords.x / (width / 2.0) - 1,
            1 - coords.y / (height / 2.0)
        )
    
    def unit2Canvas(self, coords : vec2) -> vec2:
        # Map opengl screen coords [-1.0 -> 1.0] to screen pixel coordinates
        # In OpenGL, y goes positive upwards
        width = self.winfo_width()
        height = self.winfo_height()
        
        return vec2(
            (coords.x + 1.) * (width / 2.),
            (1 - coords.y) * (height / 2.)
        )
    
    def world2Canvas(self, coords : vec3) -> vec2:
        MVP = self.PMatrix * self.MVMatrix
        unitCoords = (MVP * vec4(coords, 1)).xy

        return self.unit2Canvas(unitCoords)

    def canvas2World(self, coords : vec2) -> vec3:
        coordsUnit = self.canvas2Unit(coords)
        
        MVPinv = inverse(self.PMatrix * self.MVMatrix)
        
        return (MVPinv * vec4(coordsUnit, 0, 1)).xyz
    
    def canvas2WorldXY(self, coords : vec2) -> vec2:
        # Proyect canvas coords to the world xy plane
        coordsUnit = self.canvas2Unit(coords)
        
        MVPinv = inverse(self.PMatrix * self.MVMatrix)

        # We define a line perpendicular to the canvas
        p1 = (MVPinv * vec4(coordsUnit, 0, 1)).xyz
        p2 = (MVPinv * vec4(coordsUnit, 1, 1)).xyz
        
        direction = p2 - p1

        # If we are almost parallel to the XY plane (<10º), return None
        angleXY = 90 - numpy.rad2deg(numpy.acos(abs(dot(normalize(direction), vec3(0, 0, 1)))))
        if angleXY < 10:
            return None
    
        t = -p1.z / direction.z
        return (p1 + t * direction).xy
    
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
        
        self.cameraPosition()

        self.queueDraw()
        
        # TODO: Implement the rest
        return

        x0 = self.canvasx(0)
        y0 = self.canvasy(0)

        # Update last insert
        if self._lastGantry:
            self.updateGantry(*self.plotCoords([self._lastGantry])[0])
        else:
            self.updateGantry(0, 0)

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
        """
        Zoom to Fit to Screen
        """
        
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
        
        self.zoom = min(width, height) / self._modelSize
        
        self.PMatrix = ortho(-width / 2.0 / self.zoom, 
                             width / 2.0 / self.zoom, 
                             -height / 2.0 / self.zoom,
                             height / 2.0 / self.zoom, 
                             -10000,
                             10000)

        self.cameraPosition()
        self.queueDraw()

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
                self.set_arrow(self.pathArrows, self.pathArrowsVBO, self.pathVertices, self._lastActive, 'none')
            self._lastActive = item
            self.set_arrow(self.pathArrows, self.pathArrowsVBO, self.pathVertices, self._lastActive, 'last', 10, 10)

    # ----------------------------------------------------------------------
    # Display gantry
    # ----------------------------------------------------------------------
    def gantry(self, wx, wy, wz, mx, my, mz):
        self._lastGantry = (wx, wy, wz)
        self.updateGantry(wx, wy, wz)
        if self._showCamera and self.cameraAnchor == NONE:
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
            self.set_arrow(self.pathArrows, self.pathArrowsVBO, self.pathVertices, self._lastActive, 'none')
            self._lastActive = None
        
        self.deselectAll(self.pathVertices, self.pathVBO)
         
        self.deleteInfo()
        

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
        
        self.setFlags(self.pathVertices, FLAG_SELECTED | FLAG_ENABLED, linesAndFlags, self.pathVBO)

        # Update arrows, if any
        self.update_arrows_from_lines(self.pathArrows, self.pathArrowsVBO, self.pathVertices)
                
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

    def deleteLines(self, lines, linesVertices, linesBuffer, updateModelDimensions = False):
        lines.clear()
        linesVertices = self.update_lines_buffer(linesBuffer, lines, updateModelDimensions)

        return linesVertices
    
    def deleteArrows(self, arrows, arrowsBuffer):
        arrows.clear()
        self.update_arrows_buffer(arrowsBuffer, arrows)

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
        # TODO: implement
        #self.itemconfig("Orient", width=1)
        if marker >= 0:
            self._orientSelected = marker
            try:
                for i in self.gcode.orient.paths[self._orientSelected]:
                    # TODO: Implement
                    pass
                    # self.itemconfig(i, width=2)
            except IndexError:
                self.drawOrient()
        else:
            self._orientSelected = None

    # ----------------------------------------------------------------------
    # Display graphical information on selected blocks
    # ----------------------------------------------------------------------
    def showInfo(self, blocks):
        # Clear any previous information
        self.infoLines = {}

        self.deleteArrows(self.infoArrows, self.infoArrowsVBO)


        infoArcs = []

        for bid in blocks:
            block = self.gcode.blocks[bid]
            xyz = [
                (block.xmin, block.ymin, 0.0),
                (block.xmax, block.ymin, 0.0),
                (block.xmax, block.ymax, 0.0),
                (block.xmin, block.ymax, 0.0),
                (block.xmin, block.ymin, 0.0),
            ]

            self.create_line(self.infoLines,
                             xyz,
                             self.rgb8(INFO_COLOR),
                             1)
            
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

            infoArcs.append(self.create_line(
                self.infoLines,
                xyz,
                self.rgb8(INFO_COLOR),
                1
            ))
        
        self.infoVertices = self.update_lines_buffer(self.infoVBO, self.infoLines)

        for arc in infoArcs:
            self.set_arrow(self.infoArrows, self.infoArrowsVBO, self.infoVertices, arc, 'last', 20, 20)

        self.queueDraw()
    
    def deleteInfo(self):
        self.showInfo([])

    # -----------------------------------------------------------------------
    def cameraOn(self, event=None):
        if not self.camera.start():
            return
        self.cameraRefresh()

    # -----------------------------------------------------------------------
    def cameraOff(self, event=None):
        self._showCamera = False

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

        if not self._showCamera:
            self._showCamera = True
        
        self.cameraPosition()

        try:
            self.cameraImage = self.get_camera_image()
            glActiveTexture(GL_TEXTURE0)
            glBindTexture(GL_TEXTURE_2D, self.cameraTexture)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST)
            glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA,
                         len(self.cameraImage[0]),
                         len(self.cameraImage),
                         0, GL_RGBA, GL_UNSIGNED_BYTE, self.cameraImage)
            
            self.queueDraw()

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
        if not self._showCamera:
            return
        
        w = self.winfo_width()
        h = self.winfo_height()
        hc, wc = self.camera.image.shape[:2]
        zoomx = self.PMatrix[0][0]
        zoomy = self.PMatrix[1][1]
        wc *= 0.5 / self.cameraScale * zoomx * w / 2.
        hc *= 0.5 / self.cameraScale * zoomy * h / 2.
        x = w / 2  # everything on center
        y = h / 2

        if self.cameraAnchor == NONE: # Center on Gantry
            dx = dy = 0
            if not self.cameraSwitch:
                dx = self.cameraDx
                dy = self.cameraDy

            x, y = self.world2Canvas(vec3(self._gantryLocation) + vec3(dx, dy, 0))
            
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
        
        self.cameraLocation = vec2(x, y)

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
        glDepthFunc(GL_LEQUAL)
        
        # Draw background
        glUseProgram(self.backgroundProgram)
        glBindBuffer(GL_ARRAY_BUFFER, self.backgroundVBO)
        glVertexAttribPointer(glGetAttribLocation(self.backgroundProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, 6*4, c_void_p(0*4))
        glVertexAttribPointer(glGetAttribLocation(self.backgroundProgram, "color"), 3, GL_FLOAT, GL_FALSE, 6*4, c_void_p(3*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.backgroundProgram, "xyz"))
        glEnableVertexAttribArray(glGetAttribLocation(self.backgroundProgram, "color"))
        glDrawArrays(GL_TRIANGLES, 0, 6)

        # Ensure that the next items are drawn on top of this
        glClear(GL_DEPTH_BUFFER_BIT)

        # Draw Camera
        if self._showCamera:
            glDisable(GL_CULL_FACE)
            glUseProgram(self.ImageProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.CameraVBO)
            PARAMETERS_PER_VERTEX = 1
            glVertexAttribPointer(glGetAttribLocation(self.ImageProgram, "index"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glEnableVertexAttribArray(glGetAttribLocation(self.ImageProgram, "index"))

            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.ImageProgram, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

            location_loc = glGetUniformLocation(program=self.ImageProgram, name="location")
            glUniform2fv(location_loc, 1, value_ptr(self.cameraLocation))

            # Set the uniform variable 'ourTexture' to texture unit 0
            glActiveTexture(GL_TEXTURE0)
            glBindTexture(GL_TEXTURE_2D, self.cameraTexture)
            glUniform1i(glGetUniformLocation(self.ImageProgram, "ourTexture"), 0)

            width_loc = glGetUniformLocation(program=self.ImageProgram, name="width")
            glUniform1f(width_loc, len(self.cameraImage[0]))

            height_loc = glGetUniformLocation(program=self.ImageProgram, name="height")
            glUniform1f(height_loc, len(self.cameraImage))

            canvasWidth_loc = glGetUniformLocation(program=self.ImageProgram, name="canvasWidth")
            glUniform1f(canvasWidth_loc, self.winfo_width())

            canvasHeight_loc = glGetUniformLocation(program=self.ImageProgram, name="canvasHeight")
            glUniform1f(canvasHeight_loc, self.winfo_height())

            # We get the zoom from the projection matrix
            zoomx = self.PMatrix[0][0]
            zoomy = self.PMatrix[1][1]
            zoom_loc = glGetUniformLocation(program=self.ImageProgram, name="zoom")
            glUniform2f(zoom_loc, zoomx, zoomy)
            
            cameraScale_loc = glGetUniformLocation(program=self.ImageProgram, name="cameraScale")
            glUniform1f(cameraScale_loc, self.cameraScale)

            glDrawArrays(GL_TRIANGLES, 0, 6)

            # Ensure that the next items are drawn on top of this
            glClear(GL_DEPTH_BUFFER_BIT)
        
        # Draw Crosshair
        if self._showCamera:
            glUseProgram(self.CrossHairProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.CrossHairVBO)
            PARAMETERS_PER_VERTEX = 1
            glVertexAttribPointer(glGetAttribLocation(self.CrossHairProgram, "index"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glEnableVertexAttribArray(glGetAttribLocation(self.CrossHairProgram, "index"))

            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.CrossHairProgram, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

            location_loc = glGetUniformLocation(program=self.CrossHairProgram, name="location")
            glUniform2fv(location_loc, 1, value_ptr(self.cameraLocation))

            width_loc = glGetUniformLocation(program=self.CrossHairProgram, name="width")
            glUniform1f(width_loc, len(self.cameraImage[0]))

            height_loc = glGetUniformLocation(program=self.CrossHairProgram, name="height")
            glUniform1f(height_loc, len(self.cameraImage))

            canvasWidth_loc = glGetUniformLocation(program=self.CrossHairProgram, name="canvasWidth")
            glUniform1f(canvasWidth_loc, self.winfo_width())

            canvasHeight_loc = glGetUniformLocation(program=self.CrossHairProgram, name="canvasHeight")
            glUniform1f(canvasHeight_loc, self.winfo_height())

            R_loc = glGetUniformLocation(program=self.CrossHairProgram, name="R")
            glUniform1f(R_loc, self.cameraR)

            # We get the zoom from the projection matrix
            zoomx = self.PMatrix[0][0]
            zoomy = self.PMatrix[1][1]
            zoom_loc = glGetUniformLocation(program=self.CrossHairProgram, name="zoom")
            glUniform2f(zoom_loc, zoomx, zoomy)

            cameraScale_loc = glGetUniformLocation(program=self.CrossHairProgram, name="cameraScale")
            glUniform1f(cameraScale_loc, self.cameraScale)

            glLineWidth(1.5)
            size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
            glDrawArrays(GL_LINES, 0, size // PARAMETERS_PER_VERTEX)

            # Ensure that the next items are drawn on top of this
            glClear(GL_DEPTH_BUFFER_BIT)

        # Draw grid
        if self.draw_grid:
            glUseProgram(self.gridProgram)
            glBindBuffer(GL_ARRAY_BUFFER, self.gridVBO)
            PARAMETERS_PER_VERTEX = 4
            glVertexAttribPointer(glGetAttribLocation(self.gridProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
            glVertexAttribPointer(glGetAttribLocation(self.gridProgram, "position"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
            glEnableVertexAttribArray(glGetAttribLocation(self.gridProgram, "xyz"))
            glEnableVertexAttribArray(glGetAttribLocation(self.gridProgram, "position"))
            
            MVP = self.PMatrix * self.MVMatrix
            mv_loc = glGetUniformLocation(program=self.gridProgram, name="MVP")
            glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
            
            zoom_loc = glGetUniformLocation(program=self.gridProgram, name="zoom")
            glUniform1f(zoom_loc, self.zoom)
            
            glLineWidth(2)
            glEnable(GL_LINE_SMOOTH)
            glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
            glDrawArrays(GL_LINES, 0, len(self.gridVertices) // PARAMETERS_PER_VERTEX)
            glBindBuffer(GL_ARRAY_BUFFER, 0)
        
        # Draw margins
        if self.draw_margin:
            self.drawLines(self.marginsVBO, 1)
        
        # Draw work area
        if self.draw_workarea:
            self.drawLines(self.workAreaVBO, 1)
        
        # Draw orient markers
        glClear(GL_DEPTH_BUFFER_BIT)
        self.drawLines(self.orientVBO, 5)
        
        # Draw path
        glClear(GL_DEPTH_BUFFER_BIT)
        if self.pathVertices.size > 0:
            self.drawLines(self.pathVBO, 2)
        
        # Draw arrows
        if len(self.pathArrows) > 0:
            self.drawArrows(self.pathArrowsVBO)
        
        # Draw probe grid, map and text
        if self.draw_probe:
            self.drawLines(self.probeVBO, 1)
            self.drawProbeMap()
            self.drawText(self.ProbeTextVBO)

        # Draw info lines
        if self.infoVertices.size > 0:
            self.drawLines(self.infoVBO, 2)
        
        # Draw info arrows
        if len(self.infoArrows) > 0:
            self.drawArrows(self.infoArrowsVBO)
        
        # Draw Text
        if len(self.text) > 0:
            self.drawText(self.TextVBO)

        # Draw axes
        if self.draw_axes:
            self.drawAxes()
        
        # Draw gantry
        self.drawGantry()
        
        # Draw selection rectangle
        if self._mouseAction == ACTION_SELECT_AREA:
            self.drawSelectionRectangle()

        glUseProgram(0)
        
        self.swap_buffers()
        
        self._drawRequested = False
    
    def drawSelectionRectangle(self):
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

    def drawLines(self, vbo, lineWidth):
        glEnable(GL_DEPTH_TEST)
        glUseProgram(self.linesProgram)
        glBindBuffer(GL_ARRAY_BUFFER, vbo)
        PARAMETERS_PER_VERTEX = 8
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "id"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "xyz"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(1*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "pos"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(4*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "colorValue"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(5*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "dashRatio"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(6*4))
        glVertexAttribPointer(glGetAttribLocation(self.linesProgram, "flags"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(7*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "id"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "xyz"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "pos"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "colorValue"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "dashRatio"))
        glEnableVertexAttribArray(glGetAttribLocation(self.linesProgram, "flags"))


        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.linesProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

        zoom_loc = glGetUniformLocation(program=self.linesProgram, name="zoom")
        glUniform1f(zoom_loc, self.zoom)

        glLineWidth(lineWidth)
        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_LINES, 0, size // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
    
    def drawGantry(self):
        glUseProgram(self.gantryProgram)
        glEnable(GL_CULL_FACE)
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

        diameter = max(6., CNC.vars["diameter"])
        diameter_loc = glGetUniformLocation(program=self.gantryProgram, name="diameter")
        glUniform1f(diameter_loc, diameter)
        
        glLineWidth(2)
        glEnable(GL_LINE_SMOOTH)
        glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_TRIANGLES, 0, size // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)

    def drawArrows(self, vbo):
        glEnable(GL_DEPTH_TEST)
        glDisable(GL_CULL_FACE)
        glUseProgram(self.ArrowProgram)
        glBindBuffer(GL_ARRAY_BUFFER, vbo)
        PARAMETERS_PER_VERTEX = 12
        #glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "id"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "index"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(1*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "location"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(2*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "dir"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(5*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "width"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(8*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "height"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(9*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "colorValue"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(10*4))
        glVertexAttribPointer(glGetAttribLocation(self.ArrowProgram, "flags"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(11*4))
        #glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "id"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "index"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "location"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "dir"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "width"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "height"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "colorValue"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ArrowProgram, "flags"))


        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.ArrowProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))
        
        MVPinv = inverse(MVP)
        mvpinv_loc = glGetUniformLocation(program=self.ArrowProgram, name="MVPinv")
        glUniformMatrix4fv(mvpinv_loc, 1, False, value_ptr(MVPinv))

        zoom_loc = glGetUniformLocation(program=self.ArrowProgram, name="zoom")
        glUniform1f(zoom_loc, self.zoom)

        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_TRIANGLES, 0, size // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)
    
    def drawAxes(self):
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
        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_LINES, 0, size // PARAMETERS_PER_VERTEX)
        glBindBuffer(GL_ARRAY_BUFFER, 0)

        # Draw axes text. Update text location with the current zoom
        self.axesText[1][0] = vec3(AXIS_LENGTH / self.zoom, 0, 0)
        self.axesText[2][0] = vec3(0, AXIS_LENGTH / self.zoom, 0)
        self.axesText[3][0] = vec3(0, 0, AXIS_LENGTH / self.zoom)
        self.update_text_buffer(self.AxesTextVBO, self.axesText)
        self.drawText(self.AxesTextVBO)
    
    def drawText(self, textBuffer):
        glDisable(GL_DEPTH_TEST)
        glDisable(GL_CULL_FACE)
        glUseProgram(self.TextProgram)
        glBindBuffer(GL_ARRAY_BUFFER, textBuffer)
        PARAMETERS_PER_VERTEX = 10
        #glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "id"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "index"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(1*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "location"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(2*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "hOffset"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(5*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "charoffset"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(6*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "charwidth"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(7*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "charheight"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(8*4))
        glVertexAttribPointer(glGetAttribLocation(self.TextProgram, "colorValue"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(9*4))
        #glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "id"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "index"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "location"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "hOffset"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "charoffset"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "charwidth"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "charheight"))
        glEnableVertexAttribArray(glGetAttribLocation(self.TextProgram, "colorValue"))

        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.TextProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

        textAtlasWidth_loc = glGetUniformLocation(program=self.TextProgram, name="textAtlasWidth")
        glUniform1f(textAtlasWidth_loc, len(self.charTextureAtlas[0]))

        canvasWidth_loc = glGetUniformLocation(program=self.TextProgram, name="canvasWidth")
        glUniform1f(canvasWidth_loc, self.winfo_width())
        canvasHeight_loc = glGetUniformLocation(program=self.TextProgram, name="canvasHeight")
        glUniform1f(canvasHeight_loc, self.winfo_height())

        # Set the uniform variable 'ourTexture' to texture unit 0
        glActiveTexture(GL_TEXTURE0)
        glBindTexture(GL_TEXTURE_2D, self.textTexture)
        glUniform1i(glGetUniformLocation(self.TextProgram, "ourTexture"), 0)
        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_TRIANGLES, 0, size // PARAMETERS_PER_VERTEX)
        
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
        self.pathVertices = self.update_lines_buffer(self.pathVBO, self.pathLines, True)
        self.updateGrid()
        self.updateMargin()
        self.updateWorkArea()

        """ self.__tzoom = 1.0
        xyz = self.canvas2xyz(
            self.canvasx(self.winfo_width() / 2),
            self.canvasy(self.winfo_height() / 2)
        )

        if view is not None:
            self.view = view

        """
        self.drawProbe()

        self.drawOrient()
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Initialize gantry position
    # ----------------------------------------------------------------------
    def initPosition(self):
        
        # TODO: Anything apart from paths must be deleted...?
        #self.delete(ALL)
        self.pathVertices = self.deleteLines(self.pathLines, self.pathVertices, self.pathVBO)
        self.deleteArrows(self.pathArrows, self.pathArrowsVBO)

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
        self.queueDraw()

    def createGantry(self):
        # Gantry geometry of diameter 1. We scale it with the actual diameter in the shader
        gr = 0.5
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
        
        gantryVertices = numpy.array(vertices, dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.gantryVBO)
        glBufferData(GL_ARRAY_BUFFER, gantryVertices.nbytes, gantryVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)

    # ----------------------------------------------------------------------
    # Create system axes
    # ----------------------------------------------------------------------
    def createAxes(self, axisLength):
        
        axesVertices = numpy.array([
            # X axis
            0, 0, 0, # Start Point
            0, # position. 0 for the first point of the line and length for the second. Used for dashed lines
            1, # Axis X
            axisLength, 0, 0, # End Point
            axisLength, # position. 0 for the first point of the line and length for the second. Used for dashed lines
            1, # Axis X
            # Y axis
            0, 0, 0, 0, 2, 0, axisLength, 0, axisLength, 2,
            # Z axis          
            0, 0, 0, 0, 3, 0, 0, axisLength, axisLength, 3
        ], dtype=numpy.float32)
        
        glBindBuffer(GL_ARRAY_BUFFER, self.axesVBO)
        glBufferData(GL_ARRAY_BUFFER, axesVertices.nbytes, axesVertices, GL_STATIC_DRAW)
        glBindBuffer(GL_ARRAY_BUFFER, 0)

        # Text (x, y, z)
        self.axesText = {
            1: [vec3(axisLength * self.zoom, 0, 0), "X", self.rgb8("White")],
            2: [vec3(0, axisLength * self.zoom, 0), "Y", self.rgb8("White")],
            3: [vec3(0, 0, axisLength * self.zoom), "Z", self.rgb8("White")]
            }
        self.update_text_buffer(self.AxesTextVBO, self.axesText)

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
        
        marginLines = {}

        if CNC.isMarginValid():
            xyz = [[CNC.vars["xmin"], CNC.vars["ymin"], 0.0],
                [CNC.vars["xmax"], CNC.vars["ymin"], 0.0],
                [CNC.vars["xmax"], CNC.vars["ymax"], 0.0],
                [CNC.vars["xmin"], CNC.vars["ymax"], 0.0],
                [CNC.vars["xmin"], CNC.vars["ymin"], 0.0]]
        
            self.create_line(marginLines, xyz, (255, 0, 255), 1)
            self.update_lines_buffer(self.marginsVBO, marginLines)

        if not CNC.isAllMarginValid():
            self.queueDraw()
            return
        
        xyz = [[CNC.vars["axmin"], CNC.vars["aymin"], 0.0],
                [CNC.vars["axmax"], CNC.vars["aymin"], 0.0],
                [CNC.vars["axmax"], CNC.vars["aymax"], 0.0],
                [CNC.vars["axmin"], CNC.vars["aymax"], 0.0],
                [CNC.vars["axmin"], CNC.vars["aymin"], 0.0]]
    
        self.create_line(marginLines, xyz, (255, 0, 255), 0.66)
        self.update_lines_buffer(self.marginsVBO, marginLines)
        
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

        workAreaLines = {}

        xmin = self._dx - CNC.travel_x
        ymin = self._dy - CNC.travel_y
        xmax = self._dx
        ymax = self._dy

        xyz = [[xmin, ymin, 0.0],
            [xmax, ymin, 0.0],
            [xmax, ymax, 0.0],
            [xmin, ymax, 0.0],
            [xmin, ymin, 0.0]]
    
        self.create_line(workAreaLines, xyz, (255, 165, 0), 0.661)
        self.update_lines_buffer(self.workAreaVBO, workAreaLines)
        
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
        self.orientLines = {}

        # Draw orient markers
        if CNC.inch:
            w = 0.1
        else:
            w = 2.5

        self.gcode.orient.clearPaths()
        for i, (xm, ym, x, y) in enumerate(self.gcode.orient.markers):
            paths = []
            
            # Machine position (cross)
            item = self.create_line(self.orientLines,
                [(xm - w, ym, 0.0), (xm + w, ym, 0.0)],
                self.rgb8('Green'),
                1.)
            paths.append(item)

            item = self.create_line(self.orientLines,
                [(xm, ym - w, 0.0), (xm, ym + w, 0.0)],
                self.rgb8('Green'),
                1.)
            paths.append(item)

            # GCode position (cross)
            item = self.create_line(self.orientLines,
                [(x - w, y, 0.0), (x + w, y, 0.0)],
                self.rgb8('Red'),
                1.)
            paths.append(item)

            item = self.create_line(self.orientLines,
                [(x, y - w, 0.0), (x, y + w, 0.0)],
                self.rgb8('Red'),
                1.)
            paths.append(item)

            # Draw error if any
            try:
                err = self.gcode.orient.errors[i]
                item = self.create_oval(self.orientLines,
                    (xm - err, ym - err, 0.0),
                    (xm + err, ym + err, 0.0),
                    self.rgb8('Red'),
                    1.)
                paths.append(item)

                err = self.gcode.orient.errors[i]
                item = self.create_oval(self.orientLines,
                    (x - err, y - err, 0.0),
                    (x + err, y + err, 0.0),
                    self.rgb8('Red'),
                    1.)
                paths.append(item)
            except IndexError:
                pass

            # Connecting line
            item = self.create_line(self.orientLines,
                [(xm, ym, 0.0), (x, y, 0.0)],
                self.rgb8('LightBlue'),
                0.5)
            paths.append(item)

            self.gcode.orient.addPath(paths)

        # TODO: Implement this
        """
        if self._orientSelected is not None:
            try:
                for item in self.gcode.orient.paths[self._orientSelected]:
                    self.itemconfig(item, width=2)
            except (IndexError, TclError):
                pass
        """
        
        self.update_lines_buffer(self.orientVBO, self.orientLines)
        
        self.queueDraw()

    # ----------------------------------------------------------------------
    # Display probe
    # ----------------------------------------------------------------------
    def drawProbe(self):
        self.probeLines = {}
        #self.delete("Probe")
        if self._probe:
            #self.delete(self._probe)
            self._probe = None
        if not self.draw_probe:
            self.queueDraw()
            return

        # Draw probe grid
        probe = self.gcode.probe
        for x in bmath.frange(probe.xmin, probe.xmax + 0.00001, probe.xstep()):
            xyz = [(x, probe.ymin, 0.0), (x, probe.ymax, 0.0)]
            item = self.create_line(
                self.probeLines,
                xyz,
                self.rgb8('Yellow'),
                1.)

        for y in bmath.frange(probe.ymin, probe.ymax + 0.00001, probe.ystep()):
            xyz = [(probe.xmin, y, 0.0), (probe.xmax, y, 0.0)]
            item = self.create_line(
                self.probeLines,
                xyz,
                self.rgb8('Yellow'),
                1.)
        
        self.update_lines_buffer(self.probeVBO, self.probeLines)

        # Lines for debugging
        """
        probe.start = True
        probe.makeMatrix()
        probe.points = []
        probe.add(500, 235, 3.7)
        probe.add(725, 235, -2.2)
        """

        # Draw probe points
        # Normalize the map height to a 10% of the minimum map side
        probeMaxZ = numpy.max(probe.matrix)
        probeMinZ = numpy.min(probe.matrix)
        probeMaxHeight = 0.1 * min(probe.xmax - probe.xmin, probe.ymax - probe.ymin)
        ratioZ = probeMaxHeight / max(abs(probeMaxZ), abs(probeMinZ))

        self.probeText = {}
        for i, location in enumerate(probe.points):
            item = self.create_text(
                self.probeText,
                vec3(location[0], location[1], location[2] * ratioZ),
                f"{probe.points[i][2]:.{CNC.digits}f}",
                self.rgb8('Yellow'))

        self.update_text_buffer(self.ProbeTextVBO, self.probeText)

        # Draw image map if numpy exists
        if (numpy is not None and probe.matrix):
            self.update_probe_map_buffer()

        self.queueDraw()

    def drawProbeMap(self):
        glEnable(GL_DEPTH_TEST)
        glDisable(GL_CULL_FACE)
        glUseProgram(self.ProbeMapProgram)
        glBindBuffer(GL_ARRAY_BUFFER, self.ProbeMapVBO)
        PARAMETERS_PER_VERTEX = 4
        glVertexAttribPointer(glGetAttribLocation(self.ProbeMapProgram, "location"), 3, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, None)
        glVertexAttribPointer(glGetAttribLocation(self.ProbeMapProgram, "colorValue"), 1, GL_FLOAT, GL_FALSE, PARAMETERS_PER_VERTEX*4, c_void_p(3*4))
        glEnableVertexAttribArray(glGetAttribLocation(self.ProbeMapProgram, "location"))
        glEnableVertexAttribArray(glGetAttribLocation(self.ProbeMapProgram, "colorValue"))

        MVP = self.PMatrix * self.MVMatrix
        mv_loc = glGetUniformLocation(program=self.ProbeMapProgram, name="MVP")
        glUniformMatrix4fv(mv_loc, 1, False, value_ptr(MVP))

        maxZ_loc = glGetUniformLocation(program=self.ProbeMapProgram, name="maxZ")
        glUniform1f(maxZ_loc, self.probeMaxZ)

        minZ_loc = glGetUniformLocation(program=self.ProbeMapProgram, name="minZ")
        glUniform1f(minZ_loc, self.probeMinZ)

        maxHeight_loc = glGetUniformLocation(program=self.ProbeMapProgram, name="maxHeight")
        glUniform1f(maxHeight_loc, self.probeMaxHeight)

        alpha_loc = glGetUniformLocation(program=self.ProbeMapProgram, name="alpha")
        glUniform1f(alpha_loc, 0.5)

        size = glGetBufferParameteriv(GL_ARRAY_BUFFER, GL_BUFFER_SIZE) // 4
        glDrawArrays(GL_TRIANGLES, 0, size // PARAMETERS_PER_VERTEX)

    def update_probe_map_buffer(self):
        probe = self.gcode.probe

        self.probeMaxZ = numpy.max(probe.matrix)
        self.probeMinZ = numpy.min(probe.matrix)

        # Normalize the map height to a 10% of the minimum map side
        self.probeMaxHeight = 0.1 * min(probe.xmax - probe.xmin, probe.ymax - probe.ymin)

        probeMapData = []

        # Each quad of the map is drawn as two triangles (6 vertices)
        for j in range(probe.yn - 1):
            for i in range(probe.xn - 1):
                color1 = self.blue2red(probe.matrix[j][i], self.probeMinZ, self.probeMaxZ)
                color2 = self.blue2red(probe.matrix[j][i + 1], self.probeMinZ, self.probeMaxZ)
                color3 = self.blue2red(probe.matrix[j + 1][i + 1], self.probeMinZ, self.probeMaxZ)
                color4 = self.blue2red(probe.matrix[j + 1][i], self.probeMinZ, self.probeMaxZ)
                probeMapData.extend([
                    # Corner 1
                    probe.xmin + i * probe.xstep(),
                    probe.ymin + j * probe.ystep(),
                    probe.matrix[j][i],
                    (int(color1.x) << 16) + (int(color1.y) << 8) + int(color1.z),
                    # Corner 2
                    probe.xmin + (i + 1) * probe.xstep(),
                    probe.ymin + j * probe.ystep(),
                    probe.matrix[j][i + 1],
                    (int(color2.x) << 16) + (int(color2.y) << 8) + int(color2.z),
                    # Corner 3
                    probe.xmin + (i + 1) * probe.xstep(),
                    probe.ymin + (j + 1) * probe.ystep(),
                    probe.matrix[j + 1][i + 1],
                    (int(color3.x) << 16) + (int(color3.y) << 8) + int(color3.z),
                    # Corner 1
                    probe.xmin + i * probe.xstep(),
                    probe.ymin + j * probe.ystep(),
                    probe.matrix[j][i],
                    (int(color1.x) << 16) + (int(color1.y) << 8) + int(color1.z),
                    # Corner 3
                    probe.xmin + (i + 1) * probe.xstep(),
                    probe.ymin + (j + 1) * probe.ystep(),
                    probe.matrix[j + 1][i + 1],
                    (int(color3.x) << 16) + (int(color3.y) << 8) + int(color3.z),
                    # Corner 4
                    probe.xmin + i * probe.xstep(),
                    probe.ymin + (j + 1) * probe.ystep(),
                    probe.matrix[j + 1][i],
                    (int(color4.x) << 16) + (int(color4.y) << 8) + int(color4.z),
                ])

        probeMapVertices = numpy.array(probeMapData, dtype=numpy.float32)

        glBindBuffer(GL_ARRAY_BUFFER, self.ProbeMapVBO)
        glBufferData(GL_ARRAY_BUFFER, probeMapVertices.nbytes, probeMapVertices, GL_STATIC_DRAW)

        glBindBuffer(GL_ARRAY_BUFFER, 0)  # Unbind the VBO

        return probeMapVertices


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
                    return self.create_line(
                        self.pathLines,
                        xyz,
                        (255, 0, 0),
                        0.5,
                        flags)
                
            elif self.draw_paths:
                return self.create_line(
                    self.pathLines,
                    xyz,
                    self.rgb8(fill),
                    1,
                    flags)
            
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
        self.canvas.queueDraw()

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
            self.canvas.queueDraw()

    # ----------------------------------------------------------------------
    def drawTimeChange(self):
        global DRAW_TIME
        try:
            DRAW_TIME = int(self.drawTime.get())
        except ValueError:
            DRAW_TIME = 5 * 60
        self.viewChange()
