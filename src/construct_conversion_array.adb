package body Construct_Conversion_Array with
SPARK_Mode
is

   ----------------------
   -- Conversion_Array --
   ----------------------

   function Conversion_Array return Conversion_Array_Type is
      Conversion_Array : Conversion_Array_Type := (others => Zero);
   begin
      for J in Product_Index_Type loop
         Conversion_Array (J) := Two_Power (Exposant (J));
         pragma Loop_Invariant (for all K in 0 .. J => Conversion_Array (K) = Two_Power (Exposant (K)));
      end loop;
      Prove_Property (Conversion_Array);
      return Conversion_Array;
   end Conversion_Array;

   --------------------
   -- Prove_Property --
   --------------------

   procedure Prove_Property (Conversion_Array : Conversion_Array_Type) is
   begin
      for J in Index_Type loop
         for K in Index_Type loop
            Exposant_Lemma (J, K);                         --  The two lemmas will help solvers
            Two_Power_Lemma (Exposant (J), Exposant (K));  --  to prove the following code.

            pragma Assert (Two_Power (Exposant (J)) = Conversion_Array (J)
                           and then Two_Power (Exposant (K)) = Conversion_Array (K)
                           and then Two_Power (Exposant (J + K)) = Conversion_Array (J + K));
            --  A reminder of the precondition

            --  The following code will split the two different cases of
            --  Property. In the statements, assertions are used to guide
            --  provers to the goal.
            if J mod 2 = 1 and then K mod 2 = 1 then
               pragma Assert (Exposant (J + K) + 1 = Exposant (J) + Exposant (K));
               pragma Assert (Two_Power (Exposant (J + K) + 1)
                              = Two_Power (Exposant (J)) * Two_Power (Exposant (K)));
               pragma Assert (Two_Power (Exposant (J + K)) * (+2)
                              = Two_Power (Exposant (J)) * Two_Power (Exposant (K)));
               pragma Assert (Property (Conversion_Array, J, K));
            else
               pragma Assert (Exposant (J + K) = Exposant (J) + Exposant (K));
               pragma Assert (Two_Power (Exposant (J + K)) = Two_Power (Exposant (J)) * Two_Power (Exposant (K)));
               pragma Assert (Property (Conversion_Array, J, K));
            end if;

            pragma Loop_Invariant (for all M in 0 .. K =>
                                     Property (Conversion_Array, J, M));
         end loop;
         pragma Loop_Invariant (for all L in 0 .. J =>
                                  (for all M in Index_Type =>
                                     Property (Conversion_Array, L, M)));
      end loop;
   end Prove_Property;
end Construct_Conversion_Array;
