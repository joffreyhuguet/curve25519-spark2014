with Big_Integers; use Big_Integers;
with Types; use Types;
with Construct_Conversion_Array;

package Conversion with
SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Conversion);

   Conversion_Array : constant Conversion_Array_Type := Construct_Conversion_Array.Conversion_Array;

   function Partial_Conversion_Rec
     (X    : Integer_Curve25519;
      L    : Product_Index_Type)
      return Big_Integer
   is
     (if L = 0 then (+X(0)) * Conversion_Array (0)
      else
         Partial_Conversion_Rec (X, L - 1) + (+X (L)) * Conversion_Array (L))
       with
         Pre  => X'First = 0 and then L in X'Range;

   function Partial_Conversion (X : Integer_Curve25519 ; L : Product_Index_Type) return Big_Integer
   is
     (Partial_Conversion_Rec (X, L))
       with
         Pre  => X'First = 0 and then L in X'Range;

   function To_Integer_256 (X : Integer_256) return Big_Integer is
     (Partial_Conversion (X, 9));

   function To_Integer_Mult (X : Product_Integer) return Big_Integer is
     (Partial_Conversion (X, 18));

   procedure Equal_To_Conversion (A, B : Integer_Curve25519; L : Product_Index_Type) with
     Pre =>
       A'Length > 0
       and then A'First = 0
       and then B'First = 0
       and then B'Last <= A'Last
       and then L in B'Range
       and then (for all J in 0 .. L => A (J) = B (J)),
       Post => Partial_Conversion (A, L) = Partial_Conversion (B, L);

   procedure Conversion_Array_Lemma (J, K : Index_Type) with
     Post => (if J mod 2 = 1 and then K mod 2 = 1
                then (+2) * Conversion_Array (J + K)
              = Conversion_Array (J) * Conversion_Array (K)
                  else Conversion_Array (J + K)
              = Conversion_Array (J) * Conversion_Array (K));
   procedure Conversion_Array_Lemma (J, K : Index_Type) is null;

end Conversion;
