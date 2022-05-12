/*
 * IdEntry.java   
 */

package VC.Checker;

import VC.ASTs.Decl;

public class IdEntry {

  protected String id;
  protected Decl attr;
  protected int level;
  protected IdEntry previousEntry;

  IdEntry (String id, Decl attr, int level, IdEntry previousEntry) {
    this.id = id;
    this.attr = attr;
    this.level = level;
    this.previousEntry = previousEntry;
  }
}
