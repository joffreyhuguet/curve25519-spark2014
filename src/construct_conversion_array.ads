with Big_Integers; use Big_Integers;
with Types       ; use Types;

package Construct_Conversion_Array with
  SPARK_Mode,
  Ghost
is
   function Property
     (Conversion_Array : Conversion_Array_Type;
      J, K             : Index_Type)
      return Boolean
   is
     (if J mod 2 = 1 and then K mod 2 = 1
      then Conversion_Array (J + K) * (+2)
           = Conversion_Array (J) * Conversion_Array (K)
      else Conversion_Array (J + K)
           = Conversion_Array (J) * Conversion_Array (K));
   --  The conversion array has a property that helps to prove
   --  the product function. This function verifies the property
   --  at index J + K.

   --------------------------
   -- Functions and lemmas --
   --------------------------

   function Two_Power (Expon : Natural) return Big_Integer is
     ((+2) ** Expon);
   --  Returns a big integer equal to 2 to the power Expon.

   procedure Two_Power_Lemma (A, B : Natural) with
     Pre => A <= Natural'Last - B,
     Post => Two_Power (A + B) = Two_Power (A) * Two_Power (B);
   procedure Two_Power_Lemma (A, B : Natural) is null;
   --  Basic property of exponentiation used in proof.

   function Exposant (J : Product_Index_Type) return Natural is
     (Natural (J) / 2 * 51 + (if J mod 2 = 1 then 26 else 0))
       with
         Post => Exposant'Result <= Natural (J) * 51;
   --  Returns the exposant of 2 at J index of conversion array.
   --  (i.e Conversion_Array (J) = Two_Power (Exposant (J)))

   procedure Exposant_Lemma (J, K : Index_Type) with
     Contract_Cases =>
       (J mod 2 = 1 and then K mod 2 = 1 => Exposant (J + K) + 1 = Exposant (J) + Exposant (K),
        others                           => Exposant (J + K) = Exposant (J) + Exposant (K));
   procedure Exposant_Lemma (J, K : Index_Type) is null;
   --  Specificity of Exposant function, that helps to prove
   --  the property.

   ----------------------------------------------------------------
   -- Computation and proof of Conversion array and its property --
   ----------------------------------------------------------------

   function Conversion_Array return Conversion_Array_Type with
     Post => (for all J in Index_Type =>
                (for all K in Index_Type =>
                     Property (Conversion_Array'Result, J, K)));
   --  Computes the conversion array

   procedure Prove_Property (Conversion_Array : Conversion_Array_Type) with
     Pre => (for all J in Product_Index_Type => Conversion_Array (J) = Two_Power (Exposant (J))),
     Post => (for all L in Index_Type =>
                (for all M in Index_Type =>
                     Property (Conversion_Array, L, M)));
   --  Helps to prove the property for all indexes of
   --  Conversion_Array. Preconditions states that
   --  the input array has the right content.
end Construct_Conversion_Array;
