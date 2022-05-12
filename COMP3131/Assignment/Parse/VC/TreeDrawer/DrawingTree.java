/*
 * DrawingTree.java       
 */

package VC.TreeDrawer;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.awt.Point;

public class DrawingTree {

  String  caption;
  int     width, height;
  Point   pos, offset;
  Polygon contour;
  DrawingTree parent;
  DrawingTree[] children;
  FontMetrics fontMetrics;
  Font font;

  public DrawingTree (String caption, int width, int height, FontMetrics fontMetrics) {
    this.caption  = caption;
    this.width    = width;
    this.height   = height;
    this.parent   = null;
    this.children = null;
    this.pos      = new Point(0, 0);
    this.offset   = new Point(0, 0);
    this.contour  = new Polygon();
    this.fontMetrics = fontMetrics;
    this.font = fontMetrics.getFont();
  }

  public void setChildren(DrawingTree[] children) {
    this.children = children;
    for (int i = 0; i < children.length; i++)
      children[i].parent = this;
  }

  private final int FIXED_FONT_HEIGHT = 10;
  private final int FIXED_FONT_ASCENT = 3;
  private final Color nodeColor = new Color(255, 255, 255);

  public void paint (Graphics graphics) {
    graphics.setFont(font);
    graphics.setColor(nodeColor);
    graphics.fillRect(pos.x, pos.y, width, height);
    graphics.setColor(Color.black);
    graphics.drawRect(pos.x, pos.y, width - 1, height - 1);
    graphics.drawString(caption, pos.x + 2,
                        pos.y + (height + FIXED_FONT_HEIGHT) / 2);

    if (children != null) {
      for (int i = 0; i < children.length; i++) {
        children[i].paint(graphics);
      }
    }

    if (parent != null) {
      graphics.drawLine(pos.x + width / 2, pos.y,
                        parent.pos.x + parent.width / 2,
                        parent.pos.y + parent.height);
    }
  }

  public void position (Point pos) {

    this.pos.x = pos.x + this.offset.x;
    this.pos.y = pos.y + this.offset.y;

    Point temp = new Point(this.pos.x, this.pos.y);

    if (children != null) {
      for (int i = 0; i < children.length; i++) {
        children[i].position(temp);
        temp.x += children[i].offset.x;
        temp.y = this.pos.y + children[0].offset.y;
      }
    }
  }

}
