with Big_Integers; use Big_Integers;
with Types; use Types;

package Conversion with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Conversion);

   function Partial_Conversion_Rec
     (X    : Ints;
      L    : Index_Type_Mult)
      return Big_Integer
   is
     (if L = 0 then To_Big_Integer (X(0)) * Conversion_Array (0)
      else
         Partial_Conversion_Rec (X, L - 1) + To_Big_Integer (X (L)) * Conversion_Array (L))
       with
         Pre  => X'First = 0 and then L in X'Range;

   function Partial_Conversion (X : Ints ; L : Index_Type_Mult) return Big_Integer
   is
     (Partial_Conversion_Rec (X, L))
       with
         Pre  => X'First = 0 and then L in X'Range;

   function To_Integer_256 (X : Ints_256) return Big_Integer is
     (Partial_Conversion (X, 9));

   function To_Integer_Mult (X : Ints_Mult) return Big_Integer is
     (Partial_Conversion (X, 18));
end Conversion;
