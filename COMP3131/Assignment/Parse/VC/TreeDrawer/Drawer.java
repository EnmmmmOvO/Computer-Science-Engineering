/*
 * Drawer.java      
 */

package VC.TreeDrawer;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

import VC.ASTs.AST;

public class Drawer {

  private DrawerFrame frame;
  private DrawerPanel panel;

  private AST theAST;
  private DrawingTree theDrawing;

  private boolean debug;

  public Drawer() {
    debug = false; // do not draw SourcePosition
  }

  public void enableDebugging() {
    debug = true;
  }
  
  // Draw the AST representing a complete program.

  public void draw(AST ast) {
    theAST = ast;
    panel = new DrawerPanel(this);
    panel.setBackground(Color.white);

    frame = new DrawerFrame(panel);

    Font font = new Font("Times", Font.BOLD, 12);
    frame.setFont(font);

    FontMetrics fontMetrics = frame.getFontMetrics(font);

    LayoutVisitor layout = new LayoutVisitor(fontMetrics);
    if (debug)
      layout.enableDebugging();
    theDrawing = (DrawingTree) theAST.visit(layout, null);
    theDrawing.position(new Point(500, 10));

    frame.setVisible(true);

  }

  public void paintAST (Graphics g) {
    g.setColor(Color.white);
    g.setColor(panel.getBackground());
    Dimension d = panel.getSize();
    g.fillRect(0, 0, d.width, d.height);

    if (theDrawing != null) {
      theDrawing.paint(g);
    }
  }
}
