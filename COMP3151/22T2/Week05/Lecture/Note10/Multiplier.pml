//This is not a stand-alone model.

proctype Multiplier(byte Coeff;
                    chan North;
                    chan East;
                    chan South;
                    chan West)
{
  byte Sum, X;
  for (i : 0..(SIZE-1)) {
    if :: North ? X -> East ? Sum;
       :: East  ? Sum -> North ? X;
    fi;
    South ! X;
    Sum = Sum + X*Coeff;
    West  ! Sum;
  }
}