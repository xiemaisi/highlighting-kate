// from https://semmle.com/custom-analysis-for-heartbleed/

import cpp

/** Could e evaluate to a pointer into a buffer referenced by v? */
predicate pointsInto(Expr e, Variable v) {
  e = v.getAnAccess() or
  exists (ArrayExpr ae | ae = ((AddressOfExpr)e).getOperand() | ae.getArrayBase() = v.getAnAccess()) or
  pointsInto(((VariableAccess)e).getTarget().getAnAssignedValue(), v)
}

/** Is v ever (implicitly or explicitly) compared to w?*/
predicate comparedTo(Variable v, Variable w) {
  v.getAnAssignedValue() = w.getAnAccess() or
  exists (ComparisonOperation comp |
    comp = v.getAnAccess().getParent+() and
    comp = w.getAnAccess().getParent+()
  )
}

/** Is 'memcpy' a memcpy operation reading from f? */
predicate memcpy(FunctionCall memcpy, Field f) {
  memcpy.getTarget().getName().matches("%memcpy%") and
  pointsInto(memcpy.getArgument(1), f)
}
 
/** Is 'memcpy' a memcpy operation reading from f with a bounds check against g? */
predicate guarded_memcpy(FunctionCall memcpy, Field f, Field g) {
  memcpy(memcpy, f) and
  comparedTo(((VariableAccess)memcpy.getArgument(2)).getTarget(), g)
}

/** Are memcpy operations reading from f usually (i.e., in more than 50% of cases)
 * guarded by bounds checks against g? If so, bind 'p' to the percentage of checked
 * memcpy operations. */
predicate memcpy_usually_guarded(Field f, Field g, float p) {
  exists (int total, int guarded |
      total = count(FunctionCall fc | memcpy(fc, f)) and
      guarded = count(FunctionCall fc | guarded_memcpy(fc, f, g)) and
      p = ((float)guarded*100)/total and
      p > 50
  )
}

// find memcpy operations reading from a field f that are not bounds-checked against field g,
// where more than 50% of all memcpy reads from f do have such a check
from FunctionCall memcpy, Struct s, Field f, Field g, float perc
where f = s.getAField() and g = s.getAField() and
      memcpy(memcpy, f) and
      memcpy_usually_guarded(f, g, perc) and
      not guarded_memcpy(memcpy, f, g) and
      forall (Field gg, float pperc | memcpy_usually_guarded(f, gg, pperc) | pperc <= perc)
select memcpy, "memcpy from " + s.toString() + "::" + f +
               " is guarded by comparison against " + s.toString() + "::" + g +
               " in " + perc + "% of all cases, but not here."