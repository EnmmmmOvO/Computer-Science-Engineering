/*
 * DrawerFrame.java       
 */

package VC.TreeDrawer;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

class DrawerFrame extends JFrame {
  public DrawerFrame (JPanel panel) {
    setSize(1000, 800);
    Toolkit tk = Toolkit.getDefaultToolkit();
    Dimension d = tk.getScreenSize();
    int screenHeight = d.height;
    int screenWidth = d.width;
    setTitle("The VC Compiler Abstract Syntax Tree");
    setSize((screenWidth * 9)/10, (screenHeight * 9)/10);
    setLocation(screenWidth / 20, screenHeight / 20);
    // Image img = tk.getImage("icon.gif");
    // setIconImage(img);

    addWindowListener(
      new WindowAdapter() {
        public void windowClosing (WindowEvent e) {
      	  System.exit(0);
        }
      }
    );
    Container contentPane = getContentPane();
    contentPane.add(new JScrollPane(panel));
  }
}
