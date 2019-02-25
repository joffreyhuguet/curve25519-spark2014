with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519 with
  SPARK_Mode
is

   Min_Add : constant Long_Long_Integer := -2**30 + 1 with Ghost;
   Max_Add : constant Long_Long_Integer := 2**30 - 1 with Ghost;
   Min_Multiply : constant Long_Long_Integer := -2**27 + 1 with Ghost;
   Max_Multiply : constant Long_Long_Integer := 2**27 - 1 with Ghost;

   function Add (X, Y : Ints_256) return Ints_256 with
     Pre  => (for all J in X'Range =>
                X (J) in Min_Add .. Max_Add
                and then Y (J) in Min_Add .. Max_Add),
     Post => To_Integer_256 (Add'Result) =
               To_Integer_256 (X) + To_Integer_256 (Y);

   function Multiply (X, Y : Ints_256) return Ints_Mult with
     Pre  => (for all J in X'Range =>
                X (J) in Min_Multiply .. Max_Multiply
              and then Y (J) in Min_Multiply .. Max_Multiply),
     Post => To_Integer_Mult (Multiply'Result) =
               To_Integer_256 (X) * To_Integer_256 (Y);

end Curve25519;
