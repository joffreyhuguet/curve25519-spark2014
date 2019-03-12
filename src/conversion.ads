with Big_Integers; use Big_Integers;
with Types;        use Types;
with Construct_Conversion_Array;

package Conversion with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Conversion);

   Conversion_Array : constant Conversion_Array_Type := Construct_Conversion_Array.Conversion_Array;
   --  Conversion_Array is the array constructed in the
   --  Construct_Conversion_Array package. It has the
   --  property proven in the previous package.
   --
   --  Conversion_Array = (1, 2**25, 2**51, 2**77, 2**102, 2**128, 2**153,
   --                      2**179, 2**204, 2**230, 2**255, 2**281, 2**306,
   --                      2**332, 2**357, 2**383, 2**408, 2**434, 2**459)


   function Partial_Conversion_Rec
     (X : Integer_Curve25519;
      L : Product_Index_Type)
      return Big_Integer
   is
     (if L = 0
      then (+X(0)) * Conversion_Array (0)
      else
         Partial_Conversion_Rec (X, L - 1) + (+X (L)) * Conversion_Array (L))
   with
     Pre => L in X'Range;
   --  Recursive function to convert the array of integers to the integer
   --  it represents.

   function Partial_Conversion
     (X : Integer_Curve25519;
      L : Product_Index_Type)
      return Big_Integer
   is
     (Partial_Conversion_Rec (X, L))
   with
     Pre => L in X'Range;
   --  Wrapper for recursive function Partial_Conversion_Rec

   function To_Big_Integer (X : Integer_Curve25519)
     return Big_Integer
   is
     (Partial_Conversion (X, X'Last))
   with
     Pre => X'Length > 0;
   --  Converts an array of 10 32-bits integers to the signed
   --  256-bits integer it represents.

   procedure Equal_To_Conversion
     (A, B : Integer_Curve25519;
      L    : Product_Index_Type)
   with
     Pre  =>
       A'Length > 0
       and then A'First = 0
       and then B'First = 0
       and then B'Last <= A'Last
       and then L in B'Range
       and then (for all J in 0 .. L => A (J) = B (J)),
     Post => Partial_Conversion (A, L) = Partial_Conversion (B, L);
   --  Lemma to prove that if A (0 .. L) = B (0 .. L) then
   --  Partial_Conversion (A, L) = Partial_Conversion (B, L).
end Conversion;
