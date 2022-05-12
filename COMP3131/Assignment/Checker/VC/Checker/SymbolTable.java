/*
 * SymbolTable.java 
 *
 * In the current implementation, there is only one symbol table for
 * the entire program being compiled. It is a stack in which each
 * entry contains an identifier, a scope level and a declaration.
 *
 * There are four methods:
 * insert:    push a new entry (id, attr) to the stack
 * retrieve:  return the top-most entry for an identifier
 * openScope: increment the current scope level by 1 
 * closeScope: pop off all entries in the current scope level
 *
 *
 * In an industry compiler for a block-structured language, it is
 * common to build a new symbol table for each scope and link the
 * tables from inner to outer scopes together so that the retrieve
 * operation will automatically continue the search with an enclosing
 * table if it fails to find the identifier in the current table.
 *
 * In some languages, leaving a scope does not necessarily mean that 
 * the scope can be permanently destroyed. For example, in languages
 * such as Java and Ada, it is possible to use a quantified name 
 * such as x.y to access a nonlocal variable "y". In this case, the
 * symbol table for "y" has to be made accessible in some way.
 */

package VC.Checker;

import VC.ASTs.*;

public final class SymbolTable {

  private int level;
  private IdEntry latest;

  public SymbolTable () {
    level = 1;
    latest = null;
  }

  // Opens a new level in the symbol table, 1 higher than the
  // current topmost level.

  public void openScope () {
    level ++;
  }

  // Closes the topmost level in the symbol table, discarding
  // all entries belonging to that level.

  public void closeScope () {

    IdEntry entry;

    // Presumably, idTable.level > 0.
    entry = this.latest;
    while (entry.level == this.level)
      entry = entry.previousEntry;
    this.level--;
    this.latest = entry;
  }

  // Makes a new entry in the symbol table for the given identifier
  // and attribute. The new entry belongs to the current scope level.

  public void insert(String id, Decl attr) {

    IdEntry entry;
    entry = new IdEntry(id, attr, this.level, this.latest);
    this.latest = entry;
  }

  // Finds an entry for the given identifier in the symbol table,
  // if any. If there are several entries for that identifier, finds the
  // entry at the highest level according to the scope rules.
  // Returns null iff no entry is found.
  // otherwise returns the attribute field of the entry found.

  public Decl retrieve (String id) {

    IdEntry entry;
    Decl attr = null;
    boolean present = false, searching = true;

    entry = this.latest;
    while (searching) {
      if (entry == null)
        searching = false;
      else if (entry.id.equals(id)) {
        present = true;
        searching = false;
        attr = entry.attr;
      } else
        entry = entry.previousEntry;
    }
    return attr;
  }

 public IdEntry retrieveOneLevel(String id) {
    IdEntry entry;

    entry = this.latest;

    while (entry != null) {
      if (entry.level != this.level)
        return null;
      if (entry.id.equals(id))
        break;
      entry = entry.previousEntry;
    }

    return entry;
  }

}
