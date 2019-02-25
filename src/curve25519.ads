with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519 with
  SPARK_Mode
is

   Min_Add : constant Long_Long_Integer := -2**30 + 1;
   Max_Add : constant Long_Long_Integer := 2**30 - 1;

   function Add (X, Y : Ints_256) return Ints_256 with
     Pre  => (for all J in X'Range =>
                X (J) in Min_Add .. Max_Add
                and then Y (J) in Min_Add .. Max_Add),
     Post => ((for all J in X'Range =>
                Add'Result (J) = X (J) + Y (J)))
                and then To_Integer_256 (Add'Result) =
                            To_Integer_256 (X) + To_Integer_256 (Y);

end Curve25519;
