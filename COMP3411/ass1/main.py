from tkinter import *
from tkinter import simpledialog
from tkinter import filedialog
from PIL import Image, ImageDraw, ImageFont
import agent, RandomWalk, Qlearning, SearchAgent, WallFollow, Greedy
import gridworld, astar
import math
import platform
import dfs
import DFSAgent

DEFAULT_TILEW = 32
DEFAULT_TILEH = 32

BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0)
RED = (255, 0, 0)
YELLOW = (255, 255, 0)
GREY50 = (128, 128, 128)
LOGFILE = "./log"

if platform.system() == 'Linux':
    if "MANJARO" in platform.release():
        IMGFONT = ImageFont.truetype("/usr/share/fonts/TTF/Vera.ttf", 11)
    else:
        IMGFONT = ImageFont.truetype("/usr/share/fonts/truetype/freefont/FreeSans.ttf", 11)
elif platform.system() == 'Darwin':
    IMGFONT = ImageFont.truetype("/System/Library/Fonts/Geneva.ttf", 11)
elif platform.system() == 'Windows':
    IMGFONT = ImageFont.truetype("C:\Windows\Fonts\Arial.ttf", 11)
else:
    raise Exception("Unknown operating system")

agents = [("Random Walk", RandomWalk.RandomWalk),
          ("Search Agent", SearchAgent.SearchAgent),
          ("DFS Agent", DFSAgent.DFSAgent),
          ("Iterative Deepening DFS Agent", DFSAgent.IdDfsAgent),
          ("Q-Learning", Qlearning.Qlearning),
          ("WallFollower", WallFollow.WallFollow),
          ("Greedy", Greedy.Greedy)]

class ResizeDlg(simpledialog.Dialog):
    def __init__(self, master, w, h):
        # String variable inputs
        self.w = StringVar()
        self.w.set(w)
        
        self.h = StringVar()
        self.h.set(h)
        
        # Init
        simpledialog.Dialog.__init__(self, master, "Resize")
    
    def body(self, master):
        label = Label(master)
        label["text"] = "Width:"
        label.grid(row=0, column=0)
        
        label = Label(master)
        label["text"] = "Height:"
        label.grid(row=1, column=0)
        
        self.wentry = Entry(master)
        self.wentry["textvariable"] = self.w
        self.wentry.grid(row=0, column=1)
        
        self.hentry = Entry(master)
        self.hentry["textvariable"] = self.h
        self.hentry.grid(row=1, column=1)
        
    def apply(self):
        w = int(self.w.get())
        h = int(self.h.get())
        self.result = w, h
        
class SimulateDlg(simpledialog.Dialog):
    def __init__(self, master):
        # String variable inputs
        self.steps = StringVar()
        
        # Init
        simpledialog.Dialog.__init__(self, master, "Simulate")
        
    def body(self, master):
        label = Label(master)
        label["text"] = "Steps:"
        label.grid(row=0, column=0)
        
        self.stepentry = Entry(master)
        self.stepentry["textvariable"] = self.steps
        self.stepentry.grid(row=0, column=1)
        
        return self.stepentry
        
    def apply(self):
        self.result = int(self.stepentry.get())


class DoRunsDlg(simpledialog.Dialog):
    def __init__(self, master):
        # String variable inputs
        self.steps = StringVar()
        self.runs = StringVar()
        
        # Init
        simpledialog.Dialog.__init__(self, master, "Do Runs")
        
    def body(self, master):
        label = Label(master)
        label["text"] = "Steps:"
        label.grid(row=0, column=0)
        
        label = Label(master)
        label["text"] = "Runs:"
        label.grid(row=1, column=0)
        
        self.stepentry = Entry(master)
        self.stepentry["textvariable"] = self.steps
        self.stepentry.grid(row=0, column=1)
        
        self.runentry = Entry(master)
        self.runentry["textvariable"] = self.runs
        self.runentry.grid(row=1, column=1)
        
        return self.stepentry
        
    def apply(self):
        self.result = (int(self.stepentry.get()),
                       int(self.runentry.get()))


class TestDisplay(Toplevel):
    def __init__(self, parent, w, h, tileW, tileH, gw, tilesteps):
        """
        Creates the test result display.
        """
        Toplevel.__init__(self)
        self.title("Test Results")
        self.grab_set()
        self.transient(parent)
        
        self.bind("<Control-s>", self.cmd_save)
        self.bind("<Escape>", self.close)
        
        menu = Menu(self)
        menu.add_command(label="Save", command=self.cmd_save)
        self.config(menu=menu)
        
        cW = w * tileW
        cH = h * tileH
        
        self.canvas = Canvas(self)
        self.canvas["width"] = cW
        self.canvas["height"] = cH
        self.canvas["bg"] = "white"
        self.canvas.pack()
        
        self.image = Image.new("RGB", (cW, cH), WHITE)
        self.draw = ImageDraw.Draw(self.image)
            
        # Tiles
        for t in range(w * h):
            x, y = gw.indextopos(t)
            x *= tileW
            y *= tileH
            
            # Draw wall
            if gw.tiles[t] == gridworld.TILE_WALL:
                filled = True
                self.canvas.create_rectangle(x,
                                             y,
                                             x + tileW,
                                             y + tileH,
                                             fill="black")
                self.draw.rectangle((x,
                                     y,
                                     x + tileW,
                                     y + tileH),
                                    fill=BLACK)
            # Draw goal
            elif gw.tiles[t] == gridworld.TILE_GOAL:
                filled = True
                self.canvas.create_line(x,
                                        y,
                                        x + tileW,
                                        y + tileH,
                                        fill="black")
                self.canvas.create_line(x,
                                        y + tileH,
                                        x + tileW,
                                        y,
                                        fill="black")
                self.draw.line([x,
                                y,
                                x + tileW,
                                y + tileH],
                               fill=BLACK)
                self.draw.line([x,
                                y + tileH,
                                x + tileW,
                                y],
                               fill=BLACK)

            # Draw tiles
            else:
                optimal, steps = tilesteps[t]
                midX = x + tileW * 0.5
                midY = y + tileH * 0.5
                
                stepstr = ""
                    
                if steps < 0:
                    colorstr = "white"
                    color = WHITE
                elif steps == optimal:
                    colorstr = "green"
                    color = GREEN
                    stepstr = "+0"
                elif steps == agent.TIMEOUT:
                    colorstr = "red"
                    color = RED
                else:
                    colorstr = "yellow"
                    color = YELLOW
                    stepstr = "+{}".format(steps - optimal)
                
                self.canvas.create_rectangle(x,
                                             y,
                                             x + tileW,
                                             y + tileH,
                                             fill=colorstr)
                self.draw.rectangle((x,
                                     y,
                                     x + tileW,
                                     y + tileH),
                                    fill=color)
                
                self.canvas.create_text(midX,
                                        midY,
                                        text=stepstr,
                                        font=("FreeSans", 9))
                                        
                left, top, right, bottom = self.draw.textbbox((x, y), stepstr, font=IMGFONT)
                textW = right - left
                textH = bottom - top
                self.draw.text((midX - textW * 0.5,
                                midY - textH * 0.5),
                               stepstr,
                               font=IMGFONT,
                               fill=BLACK)
        
        # Horizontal lines
        for x in range(gw.w):
            tileX = x * tileW
            self.canvas.create_line(tileX, 0, tileX, cH, fill="grey50")
            self.draw.line([tileX, 0, tileX, cH], fill=GREY50)
        
        # Vertical lines
        for y in range(gw.h):
            tileY = y * tileH
            self.canvas.create_line(0, tileY, cW, tileY, fill="grey50")
            self.draw.line([0, tileY, cW, tileY], fill=GREY50)
            
    def cmd_save(self, event=None):
        opts = {"defaultextension": ".png", "filetypes": [("Portable Network Graphics (PNG)", ".png")], "parent": self,
                "initialdir": "./results", "title": "Save test result"}

        f = filedialog.asksaveasfilename(**opts)
        if not f: return
        
        self.save(f)
        
    def save(self, filename):
        self.image.save(filename)
        
    def close(self, event=None):
        self.destroy()


class GUI(Tk):
    def __init__(self, w = gridworld.DEFAULT_W, h = gridworld.DEFAULT_H,
                 tileW = DEFAULT_TILEW, tileH = DEFAULT_TILEH):
        Tk.__init__(self)

        # Store whether mouse is currently creating or destroying walls
        self.makewall = True
        
        # Store whether the agent is being dragged
        self.dragagent = False
        
        # ID of the running agent alarm
        self.agentalarm = None
        
        # How often the agent makes a step (in milliseconds)
        self.agentrate = 1
        
        # Whether the simulation has been started yet
        self.running = False
        
        # The currently-hovered tile
        self.cur_index = -1

        # The grid world
        self.gw = gridworld.GridWorld()

        # The current agent
        self.agent = RandomWalk.RandomWalk(self.gw)

        # The log file
        self.log = None
        self.startlog()
        
        # Set up window
        self.title("GridWorld")
        self.bind("<Escape>", self._close)
        self.bind("<Control-s>", self.cmd_save)
        self.bind("<Control-o>", self.cmd_open)
        self.bind("<Control-r>", self.cmd_resize)
        self.bind("<Return>", self.cmd_runpause)
        self.bind("<space>", self.cmd_step)
        self.bind("<r>", self.cmd_reset)
        self.bind("<s>", self.cmd_simulate)
        self.bind("<p>", self.cmd_find_path)
        self.bind("<t>", self.cmd_test)

        self.protocol("WM_DELETE_WINDOW", self._close)
        
        # Set up menu bar
        self.menu = Menu(self)
        
        submenu = Menu(self.menu, tearoff=0)
        submenu.add_command(label="Save", command=self.cmd_save)
        submenu.add_command(label="Open", command=self.cmd_open)
        self.menu.add_cascade(label="File", menu=submenu)
        
        submenu = Menu(self.menu, tearoff=0)
        submenu.add_command(label="Resize", command=self.cmd_resize)
        self.menu.add_cascade(label="Options", menu=submenu)
        
        submenu = Menu(self.menu, tearoff=0)
        for name, agent_class in agents:
            submenu.add_command(label=name,
                                command=lambda c=agent_class: self.cmd_setagent(c))
        self.menu.add_cascade(label="Agent", menu=submenu)
        
        submenu = Menu(self.menu, tearoff=0)
        submenu.add_command(label="Simulate", command=self.cmd_simulate)
        submenu.add_command(label="A* Path", command=self.cmd_find_path)
        submenu.add_command(label="Test", command=self.cmd_test)
        submenu.add_command(label="Do Runs", command=self.cmd_doruns)
        submenu.add_command(label="Average Return", command=self.cmd_avgret)
        self.menu.add_cascade(label="Simulation", menu=submenu)
        
        self.config(menu = self.menu)
        
        # Set up canvas
        self.gw.w = w
        self.gw.h = h
#        self.state_count = w * h
        self.tileW = tileW
        self.tileH = tileH
        self.canvas = Canvas(self)
        self.canvas["borderwidth"] = 1
        self.canvas["relief"] = RIDGE
        self.canvas.bind("<Button-1>", self._canv_lclick)
        self.canvas.bind("<B1-Motion>", self._canv_lmove)
        self.canvas.bind("<ButtonRelease-1>", self._canv_lrelease)
        self.canvas.bind("<Button-2>", self._canv_rclick)
        self.canvas.bind("<Motion>", self._canv_move)
        self.canvas.grid(row=0, column=1)
        
        # Set up tile info panel
        self.info_panel = Frame(self)
        self.info_panel["padx"] = 8
        self.info_panel["pady"] = 8
        self.info_panel.grid(row=0, column=0)
        
        # Set up tile info panel
        frame = LabelFrame(self.info_panel)
        frame["text"] = "Q values"
        frame["padx"] = 5
        frame["pady"] = 5
        frame.grid(row=0, column=0)
        
        label = Label(frame)
        label["text"] = "State:"
        label.grid(row=0, column=0)
        
        self.tile_type = StringVar()
        label = Label(frame)
        label["textvariable"] = self.tile_type
        label["width"] = 8
        label.grid(row=0, column=1)
        
        # Right
        label = Label(frame)
        label["text"] = "Right:"
        label.grid(row=1, column=0)
        
        self.q_right = StringVar()
        label = Label(frame)
        label["textvariable"] = self.q_right
        label["width"] = 8
        label.grid(row=1, column=1)
        
        # Up
        label = Label(frame)
        label["text"] = "Up:"
        label.grid(row=2, column=0)
        
        self.q_up = StringVar()
        label = Label(frame)
        label["textvariable"] = self.q_up
        label["width"] = 8
        label.grid(row=2, column=1)
        
        # Left
        label = Label(frame)
        label["text"] = "Left:"
        label.grid(row=3, column=0)
        
        self.q_left = StringVar()
        label = Label(frame)
        label["textvariable"] = self.q_left
        label["width"] = 8
        label.grid(row=3, column=1)
        
        # Down
        label = Label(frame)
        label["text"] = "Down:"
        label.grid(row=4, column=0)
        
        self.q_down = StringVar()
        label = Label(frame)
        label["textvariable"] = self.q_down
        label["width"] = 8
        label.grid(row=4, column=1)
        
        self.update_tileinfo()
        
        # Set up agent info
        frame = LabelFrame(self)
        frame["text"] = "Simulation options"
        frame["padx"] = 5
        frame["pady"] = 5
        frame.grid(row=1, column=1)
        
        # Set up checkboxes
        self.rand_start = BooleanVar()
        cbtn = Checkbutton(frame)
        cbtn["text"] = "Random start"
        cbtn["variable"] = self.rand_start
        cbtn["command"] = self.cmd_togglerand
        cbtn.grid(row=0, column=0)
        
        self.show_nums = BooleanVar()
        self.show_nums.set(False)
        cbtn = Checkbutton(frame)
        cbtn["text"] = "Show state"
        cbtn["variable"] = self.show_nums
        cbtn["command"] = self.redraw
        cbtn.grid(row=1, column=0)
        
        self.show_weights = BooleanVar()
        self.show_weights.set(True)
        cbtn = Checkbutton(frame)
        cbtn["text"] = "Show weights"
        cbtn["variable"] = self.show_weights
        cbtn["command"] = self.redraw
        cbtn.grid(row=2, column=0)
        
        # Set up buttons
        self.step_btn = Button(frame)
        self.step_btn["text"] = "Step"
        self.step_btn["command"] = self.cmd_step
        self.step_btn["width"] = 7
        self.step_btn.grid(row=0, column=1)
        
        self.run_btn = Button(frame)
        self.run_btn["command"] = self.cmd_runpause
        self.run_btn["width"] = 7
        self.run_btn.grid(row=1, column=1)
        
        self.reset_btn = Button(frame)
        self.reset_btn["text"] = "Reset"
        self.reset_btn["command"] = self.cmd_reset
        self.reset_btn["width"] = 7
        self.reset_btn.grid(row=2, column=1)
        
        self.update_buttons()
        
        # Set up rate scale
        self.rate_scl = Scale(frame)
        self.rate_scl["from"] = 0
        self.rate_scl["to"] = 3
        self.rate_scl["resolution"] = -1
        self.rate_scl["orient"] = HORIZONTAL
        self.rate_scl["length"] = 200
        self.rate_scl["showvalue"] = 0
        self.rate_scl["command"] = self.update_rate
        self.rate_scl.grid(row=1, column=2)
        
        self.rate_text = Label(frame)
        self.rate_text.grid(row=0, column=2)
        self.update_rate()
        
        self.agent_opts = None
        self.agent_info = None
        self.init_agent_panels()
        
        self.resize(w, h)
        
    def init_agent_panels(self):
        if self.agent_opts: self.agent_opts.destroy()
        if self.agent_info: self.agent_info.destroy()
        
        # Set up agent options
        self.agent_opts = Frame(self)
        self.agent_opts["padx"] = 8
        self.agent_opts["pady"] = 8
        self.agent_opts.grid(row=0, column=2)
        
        self.agent.init_options(self.agent_opts)
        
        # Set up agent info
        self.agent_info = LabelFrame(self.info_panel)
        self.agent_info["text"] = "Agent info"
        self.agent_info["padx"] = 5
        self.agent_info["pady"] = 5
        self.agent_info.grid(row=1, column=0)
        
        self.agent.init_info(self.agent_info)
        self.update_agentinfo()
        
    def startlog(self, name=None):
        if self.log != None:
            self.endlog()
            
        self.log = open(name if name else LOGFILE, "w")
        
    def endlog(self):
        if self.log == None: return
        
        self.log.close()
        self.log = None
        
    def resize(self, w, h, resize_gw=True):
        """
        Resize the grid and add new tiles
        """
        if resize_gw:
            self.gw.resize(w, h)
            self.rand_start.set(self.gw.agentstart == -1)
        
        newW = self.gw.w * self.tileW
        newH = self.gw.h * self.tileH
        
        # Resize canvas
        self.canvas["width"] = newW
        self.canvas["height"] = newH
        
        self.cur_index = -1
        
        self.cmd_reset()
        
    def redraw(self, event=None):
        """
        Redraw the canvas.
        """
        self.canvas.delete("all")
        self.canvas.configure(bg="white")
        cW = self.gw.w * self.tileW
        cH = self.gw.h * self.tileH
            
        # Tiles
        for t in range(self.gw.w * self.gw.h):
            x, y = self.gw.indextopos(t)
            x *= self.tileW
            y *= self.tileH
            
            filled = False
            # Draw wall
            if self.gw.tiles[t] == gridworld.TILE_WALL:
                filled = True
                self.canvas.create_rectangle(x + 1,
                                             y + 1,
                                             x + self.tileW,
                                             y + self.tileH,
                                             fill="black")
            # Draw goal
            elif self.gw.tiles[t] == gridworld.TILE_GOAL:
                filled = True
                self.canvas.create_rectangle(x + 1,
                                             y + 1,
                                             x + self.tileW,
                                             y + self.tileH,
                                             fill="green",
                                             outline="green")
            elif self.gw.agentstart == t:
                self.canvas.create_rectangle(x + 1,
                                             y + 1,
                                             x + self.tileW,
                                             y + self.tileH,
                                             fill="yellow",
                                             outline="yellow")
            # Draw beam
            elif self.gw.tiles[t] == gridworld.TILE_BEAM:
                filled = True
                self.canvas.create_rectangle(x,
                                             y,
                                             x + self.tileW,
                                             y + self.tileH,
                                             fill="grey50")

            # Draw agent
            if self.agent.state == t:
                self.agent.draw_agent(self.canvas, self.tileW, self.tileH)

                if self.agent.heading == gridworld.E:
                    self.canvas.create_line(x + 6,
                                        y + self.tileH * 0.5,
                                        x + self.tileW - 6,
                                        y + self.tileH * 0.5,
                                        arrow=LAST,
                                        arrowshape=(12, 16, 6))
                if self.agent.heading == gridworld.W:
                    self.canvas.create_line(x + 6,
                                        y + self.tileH * 0.5,
                                        x + self.tileW - 6,
                                        y + self.tileH * 0.5,
                                        arrow=FIRST,
                                        arrowshape=(12, 16, 6))

            # Draw tile insides
            if not filled:
                midX = x + self.tileW * 0.5
                midY = y + self.tileH * 0.5

                if self.show_weights.get():
                    Qs = self.agent.get_Qs(t)

                    minQ = min(Qs)

                    maxlen = -minQ + max(Qs)
                    if maxlen > 0:
                        # Draw action weights
                        for A in range(agent.ACTION_COUNT):
                            ang = A * math.pi * 0.5
                            l = (-minQ + Qs[A]) / maxlen
                            arrow = NONE if l < 1 else LAST

                            l *= min(self.tileW, self.tileH) * 0.5
                            lX = l * math.cos(ang)
                            lY = -l * math.sin(ang)

                            self.canvas.create_line(midX,
                                                    midY,
                                                    midX + lX,
                                                    midY + lY,
                                                    arrow=arrow,
                                                    arrowshape=(6,8,3))

                # Draw number
                if self.show_nums.get():
                    self.canvas.create_text(midX,
                                            midY,
                                            text = "{}".format(self.gw.tiles[t]))

        # Horizontal lines
        for x in range(self.gw.w):
            tileX = x * self.tileW
            self.canvas.create_line(tileX, 0, tileX, cH, fill="grey50")

        # Vertical lines
        for y in range(self.gw.h):
            tileY = y * self.tileH
            self.canvas.create_line(0, tileY, cW, tileY, fill="grey50")

    def update_buttons(self):
        self.run_btn["text"] = "Pause" if self.agentalarm else "Run"

    def update_rate(self, event=None):
        self.agentrate = int(10 ** self.rate_scl.get())
        self.rate_text["text"] = "Rate: {:d} ms/step".format(self.agentrate)

    def update_tileinfo(self):
        tile_type = "None"
        right = 0.0
        up = 0.0
        left = 0.0
        down = 0.0

        if self.cur_index >= 0:
            tile = self.gw.tiles[self.cur_index]

            if tile == gridworld.TILE_GOAL:
                tile_type = "Goal"
            elif tile == gridworld.TILE_WALL:
                tile_type = "Wall"
            else:
                tile_type = "{}".format(tile)

            if tile >= 0 and tile < self.gw.get_state_count():
                right, up, left, down = self.agent.get_Qs(tile)

        self.tile_type.set(tile_type)
        fmt = "{:.3f}"
        self.q_right.set(fmt.format(right))
        self.q_up.set(fmt.format(up))
        self.q_left.set(fmt.format(left))
        self.q_down.set(fmt.format(down))

    def update_agentinfo(self):
        self.agent.update_info()

    def cmd_togglerand(self, event=None):
        if self.rand_start.get():
            self.gw.agentstart = -1
        else:
            self.gw.agentstart = self.agent.state

        self.redraw()

    def cmd_runpause(self, event=None):
        # If there's an alarm running, pause
        if self.agentalarm:
            self.pause()
        else:
            self.resume()

    def cmd_reset(self, event=None):
        # Reset the agent
        self.agent.reset()
        self.gw.clear_beams()

        # Stop the agent from running
        self.pause()
        self.running = False

        # Restart log
        self.startlog()

        self.redraw()
        self.update_buttons()
        self.update_agentinfo()

    def cmd_step(self, event=None):
        self.running = True
        self.step_agent()
        self.redraw()
        self.update_agentinfo()

    def cmd_resize(self, event=None):
        resize = ResizeDlg(self, self.gw.w, self.gw.h)

        # Resize is good to go
        if resize.result:
            w, h = resize.result
            self.resize(w, h)

    def cmd_setagent(self, agentclass):
        try:
            self.agent = agentclass(self.gw)
            self.init_agent_panels()
            self.cmd_reset()
        except Exception as e:
            print(e)

    def cmd_simulate(self, event=None):
        simulate = SimulateDlg(self)

        if simulate.result:
            self.simulate(simulate.result)

    def cmd_doruns(self, event=None):
        dlg = DoRunsDlg(self)

        if dlg.result:
            self.doruns(*dlg.result)

    def cmd_avgret(self, event=None):
        dlg = DoRunsDlg(self)

        if dlg.result:
            self.avgret(*dlg.result)

    def cmd_test(self, event=None):
        # Find the goal
        goal = None
        for i, t in enumerate(self.gw.tiles):
            if t == gridworld.TILE_GOAL:
                goal = i

        if not goal:
            return

        # Set the agent to testing mode
        self.agent.set_testmode(True)

        # Check each tile
        tilesteps = [(-1, -1)] * len(self.gw.tiles)
        valid = self.gw.validtiles()
        for start in valid:
            # Run A-star to find distance
            path = astar.find_path(self.gw.immtileneighbours,
                                   start,
                                   goal,
                                   lambda tile: 1,
                                   lambda tile: not self.gw.tileblocked(*self.gw.indextopos(tile)),
                                   lambda a, b: astar.manhattan_dist(self.gw.indextopos(a),
                                                                     self.gw.indextopos(b)))

            # Run the agent from this point
            self.agent.init_episode()
            self.agent.state = start
            steps = 0
            while not self.step_agent():
                steps += 1

            # Store this in the array
            tilesteps[start] = (len(path) - 2, steps)

        # Return the agent to normal mode
        self.agent.set_testmode(False)

        # Display results
        results = TestDisplay(self, self.gw.w, self.gw.h, self.tileW, self.tileH, self.gw, tilesteps)

        self.redraw()
        self.update_agentinfo()

    def cmd_find_path(self, event=None):
        # Find the goal
        goal = None
        for i, t in enumerate(self.gw.tiles):
            if t == gridworld.TILE_GOAL:
                goal = i

        if not goal:
            return

        start = self.agent.state
        tilesteps = [(-1, -1)] * len(self.gw.tiles)

        path = astar.find_path(self.gw.immtileneighbours,
                               start,
                               goal,
                               lambda tile: 1,
                               lambda tile: not self.gw.tileblocked(*self.gw.indextopos(tile)),
                               lambda a, b: astar.manhattan_dist(self.gw.indextopos(a),
                                                                 self.gw.indextopos(b)))

        for i in path:
            steps = len(path) - 2
            tilesteps[i] = (steps, steps)

        print(path)

        # Display results
        results = TestDisplay(self, self.gw.w, self.gw.h, self.tileW, self.tileH, self.gw, tilesteps)

        self.redraw()
        self.update_agentinfo()

    def cmd_save(self, event=None):
        opts = {}
        opts["defaultextension"] = ".gwd"
        opts["filetypes"] = [("GridWorlds", ".gwd")]
        opts["parent"] = self
        opts["initialdir"] = "./worlds"
        opts["title"] = "Save world"

        f = filedialog.asksaveasfilename(**opts)
        if not f: return

        self.gw.save(f)

    def cmd_open(self, event=None):
        opts = {}
        opts["defaultextension"] = ".gwd"
        opts["filetypes"] = [("GridWorlds", ".gwd")]
        opts["parent"] = self
        opts["initialdir"] = "./worlds"
        opts["title"] = "Load world"

        f = filedialog.askopenfilename(**opts)
        if not f: return

        self.openworld(f)

    def openworld(self, f):
        self.gw.load(f)
        self.rand_start.set(self.gw.agentstart == -1)
        self.resize(self.gw.w, self.gw.h, False)

        self.redraw()

    def start_episode(self):
        self.agent.start_agent()
        self.agent.init_episode()

    def step_agent_gui(self, setalarm=True):
        self.step_agent()
        self.redraw()

        self.update_tileinfo()
        self.update_agentinfo()

        if setalarm:
            self.agentalarm = self.after(self.agentrate, self.step_agent_gui)

    def step_agent(self):
        """
        Make the agent take one step. Returns True if the agent has reached
        the goal.
        """
        self.agent.do_step(self.agent.get_state(),
                           self.agent.sample,
                           None if self.agent.testmode else self.log)

        # Start a new episode
        restarted = False
        if self.gw.tiles[self.agent.state] == gridworld.TILE_GOAL \
            or self.agent.step > agent.TIMEOUT:

            self.start_episode()
            restarted = True

        return restarted

    def simulate(self, stepcount):
        """
        Simulates stepcount steps before redrawing.
        """
        count = 0

        while count < stepcount:
            self.step_agent()
            count += 1

        self.update_agentinfo()
        self.redraw()

    def doruns(self, stepcount, runcount):
        """
        Performs the given number of stepcount runs, storing data from
        each in separate logs.
        """

        for run in range(runcount):
            self.agent.init_run()
            self.startlog("run{}".format(run))
            count = 0

            while count < stepcount:
                self.step_agent()
                count += 1

            self.endlog()

        self.update_agentinfo()
        self.redraw()

    def avgret(self, stepcount, runcount):
        """
        Performs the given number of stepcount runs, then reports the average
        return.
        """
        ret = 0

        for run in range(runcount):
            self.agent.init_run()
            count = 0

            while count < stepcount:
                self.step_agent()
                count += 1

            ret += self.agent.returnSum / self.agent.episode

        print(ret / runcount)

        self.update_agentinfo()
        self.redraw()

    def resume(self):
        """
        Resume the simulation.
        """
        # Set a new alarm
        self.agentalarm = self.after(self.agentrate, self.step_agent_gui)
        self.running = True

        self.update_buttons()

    def pause(self):
        """
        Pause the simulation.
        """
        if not self.agentalarm:
            return

        self.after_cancel(self.agentalarm)
        self.agentalarm = None

        self.update_buttons()

    def _screentotiles(self, x, y):
        return (x // self.tileW,
                y // self.tileH)

    def _canv_lclick(self, event=None):
        """
        Called when the canvas is left-clicked.
        """
        x, y = self._screentotiles(event.x, event.y)
        if not self.gw.validpos(x, y): return

        ind = self.gw.postoindex(x, y)

        # Start dragging agent
        if self.agent.state == ind:
            self.dragagent = True

        # Start making walls
        self.makewall = self.gw.tiles[ind] != gridworld.TILE_WALL

        self._canv_lmove(event)

    def _canv_lmove(self, event=None):
        """
        Called when the canvas is left-clicked and the mouse moves.
        """
        x, y = self._screentotiles(event.x, event.y)
        if not self.gw.validpos(x, y): return

        ind = self.gw.postoindex(x, y)

        # Drag agent
        if self.dragagent:
            # Don't drag into wall
            if self.gw.tiles[ind] != gridworld.TILE_WALL:
                self.agent.state = ind
                if not self.running and not self.rand_start.get():
                    self.gw.agentstart = ind

        # Draw walls
        else:
            # Can't draw over goal
            if self.gw.tiles[ind] == gridworld.TILE_GOAL or \
                self.agent.state == ind or self.gw.agentstart == ind:
                return
            
            # Make position a wall/empty
            self.gw.tiles[ind] = gridworld.TILE_WALL if self.makewall else 0
            
            # Update neighbouring tiles
            for t in self.gw.tileneighbours(ind):
                self.gw.updt_tile(t)
        
        # Redraw
        self.redraw()
        
    def _canv_lrelease(self, event=None):
        """
        Called when left-click is released on the canvas.
        """
        self.dragagent = False
        
    def _canv_rclick(self, event=None):
        """
        Called when the canvas is right-clicked.
        """
        pos = self._screentotiles(event.x, event.y)
        ind = self.gw.postoindex(*pos)
        
        # Can't put goal in a wall
        if self.gw.tiles[ind] == gridworld.TILE_WALL:
            return
        
        # Make position a goal/not a goal
        if self.gw.tiles[ind] == gridworld.TILE_GOAL:
            self.gw.tiles[ind] = ind
            self.gw.goal_state = -1
        else:
            self.gw.tiles[ind] = gridworld.TILE_GOAL
            self.gw.goal_state = ind
        
        # Redraw
        self.redraw()
        
    def _canv_move(self, event=None):
        """
        Called when the mouse moves on the canvas.
        """
        self.cur_index = -1
        
        if event:
            x, y = self._screentotiles(event.x, event.y)
            if self.gw.validpos(x, y):
                self.cur_index = min(self.gw.postoindex(x, y),
                                     len(self.gw.tiles))
                                     
        self.update_tileinfo()
            
    def _close(self, event=None):
        self.endlog()
        self.destroy()
        
app = GUI()
app.mainloop()
