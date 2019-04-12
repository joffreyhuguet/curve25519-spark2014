package body Multiply_Proof with
  SPARK_Mode
is

   ----------------------
   -- Array_Diff_Lemma --
   ----------------------

   procedure Array_Diff_Lemma
     (Previous, Conversion : Big_Integer;
      X, Y                 : Integer_255;
      J, K                 : Index_Type)
   is
   begin
      Partial_Product_Def (X, Y, J, K);
      Diff_Step_J_Def (X, Y, J, K);

      if K = 9 then
         pragma Assert (Partial_Product (X, Y, J, 9)
                        = (if J mod 2 = 1 then 2 else 1) * X (J) * Y (9));
         --  Stop case of Partial_Product (K = 9)

         pragma Assert (To_Big_Integer (Array_Step_J (X, Y, J) (J + 9))
                        = (+(if J mod 2 = 1 and then 9 mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (9)));

         pragma Assert (Diff_Step_J (X, Y, J, 9)
                        = Diff_Step_J (X, Y, J, 8)
                        + (+(if J mod 2 = 1 and then 9 mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (9))
                        * Conversion_Array (J + 9));
         --  Definition of Diff_Step_J

         pragma Assert (Conversion
                        = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + 8)
                        + Diff_Step_J (X, Y, J, 9));
         -- Proved thanks to the two assertions above
      else
         pragma Assert (Array_Step_J (X, Y, J) (J + K)
                        = Array_Step_J (X, Y, J - 1) (J + K)
                        + (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K));
         --  Definition of Partial_Product

         pragma Assert (Diff_Step_J (X, Y, J, K)
                        = (if K = 0 then Zero else Diff_Step_J (X, Y, J, K - 1))
                        + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (K))
                        * Conversion_Array (J + K));
         --  Definition of Diff_Step_J

         pragma Assert ((+Array_Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K)
                        = (+Array_Step_J (X, Y, J - 1) (J + K)) * Conversion_Array (J + K)
                        + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (K))
                        * Conversion_Array (J + K));
         --  Proved thanks to the two assertions above
      end if;
   end Array_Diff_Lemma;

   ------------------
   -- Array_Step_J --
   ------------------

   --  Construction of the array is very simple, it matches the postcondition

   function Array_Step_J
     (X, Y : Integer_255;
      J    : Index_Type)
      return Integer_Curve25519
   is
      Result : Integer_Curve25519 (0 .. J + 9) := (others => 0);
   begin
      for K in 0 .. J loop
         Result (K) := Partial_Product (X, Y, K);
         pragma Loop_Invariant (for all L in 0 .. K =>
                                  Result (L) = Partial_Product (X, Y, L));
      end loop;
      for K in J + 1 .. J + 9 loop
         Result (K) := Partial_Product (X, Y, J, K - J);
         pragma Loop_Invariant (for all L in J + 1 .. K =>
                                  Result (L) = Partial_Product (X, Y, J, L - J));
      end loop;
      return Result;
   end Array_Step_J;

   --------------------------
   -- Array_Step_J_To_Next --
   --------------------------

   procedure Array_Step_J_To_Next
     (Product_Conversion : Big_Integer;
      X, Y               : Integer_255;
      J                  : Index_Type)
   is
      Conversion, Previous : Big_Integer :=
        (if J = 0
         then Zero
         else Partial_Conversion (Array_Step_J (X, Y, J), J - 1));
   begin

      if J > 0 then
         Equal_To_Conversion
           (Array_Step_J (X, Y, J), Array_Step_J (X, Y, J - 1), J - 1);
         pragma Assert (Partial_Conversion (Array_Step_J (X, Y, J), J - 1)
                        = Partial_Conversion (Array_Step_J (X, Y, J - 1), J - 1));
         --  By definition, Array_Step_J (X, Y, J) (0 .. J - 1)
         --                 = Array_Step_J (X, Y, J - 1) (0 .. J - 1),
         --  so Equal_To_Conversion is applied to prove that their
         --  partial conversions until J - 1 are equal.
      end if;

      for K in Index_Type loop
         Previous := Conversion;
         Conversion := Conversion
                       + (+Array_Step_J (X, Y, J) (J + K))
                       * Conversion_Array (J + K);

         if J = 0 then
            Diff_Step_J_Def (X, Y, 0, K);
            Partial_Product_Def (X, Y, 0, K);
            --  Instantiating the definitions

            if K = 0 then
               pragma Assert (Conversion
                              = Partial_Conversion (Array_Step_J (X, Y, J), J + K));
               --  The assertion is needed, otherwise the solvers cannot
               --  prove first loop invariant in first iteration.
            else
               pragma Assert (Diff_Step_J (X, Y, J, K)
                              = Diff_Step_J (X, Y, J, K - 1)
                              + (+X (0)) * (+Y (K))
                              * Conversion_Array (K));
               --  Definition of Diff_Step_J

               pragma Assert (Conversion
                              = Diff_Step_J (X, Y, J, K));
               --  Discharges the provers to prove it afterwards
            end if;
         else
            Array_Diff_Lemma (Previous, Conversion, X, Y, J, K);
            --  To prove third and fourth loop invariants
         end if;

         pragma Loop_Invariant (Conversion
                                = Partial_Conversion (Array_Step_J (X, Y, J), J + K));
         --  Conversion is increasingly equal to Partial_Conversion (Array_Step_J)

         pragma Loop_Invariant (if J = 0 then Conversion = Diff_Step_J (X, Y, J, K));
         pragma Loop_Invariant (if J > 0 and then K < 9
                                then
                                   Conversion
                                   = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + K)
                                   + Diff_Step_J (X, Y, J, K));
         pragma Loop_Invariant (if J > 0 and then K = 9
                                then
                                  Conversion
                                  = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + 8)
                                  + Diff_Step_J (X, Y, J, 9));
         --  The three loop invariants above are the same loop invariant,
         --  split for different cases. It states that Conversion is equal
         --  to something + Diff_Step_J (X, Y, J, K).
      end loop;
   end Array_Step_J_To_Next;

   --------------------
   -- Prove_Multiply --
   --------------------

   procedure Prove_Multiply (X, Y : Integer_255; Product : Product_Integer) is
      X_Conversion, Product_Conversion  : Big_Integer := Zero;
      Old_X, Old_Product                : Big_Integer;
   begin
      for J in Index_Type loop
         Old_X := X_Conversion;
         X_Conversion := X_Conversion + (+X (J)) * Conversion_Array (J);
         --  X_Conversion = Partial_Conversion (X, J)
         --  is partially increased to To_Big_Integer (X).

         for K in Index_Type loop
            Old_Product := Product_Conversion;
            pragma Assert (if K = 0 then
                              Old_Product = Old_X * (+Y)
                           else Old_Product = Old_X * (+Y)
                           + (+X (J)) * Conversion_Array (J)
                           * Partial_Conversion (Y, K - 1));
            --  Asserting loop invariants on Old_Product

            Product_Conversion := Add_Factor (Product_Conversion, X, Y, J, K);
            --  Using the function is necessary to provr precondition
            --  of Split_Product.

            Diff_Step_J_Def (X, Y, J, K);
            --  To prove first loop invariant

            Split_Product (Old_Product, Old_X, Product_Conversion, X, Y, J, K);
            --  To prove second loop invariant

            pragma Loop_Invariant (Product_Conversion
                                   = Product_Conversion'Loop_Entry
                                   + Diff_Step_J (X, Y, J, K));
            --  This loop invariant is used to prove that Product_Conversion
            --  will be equal to Partial_Conversion (Array_Step_J (...))
            --  at the end of the loop.

            pragma Loop_Invariant (Product_Conversion
                                   = Old_X * (+Y)
                                   + (+X (J)) * Conversion_Array (J)
                                   * Partial_Conversion (Y, K));
            --  Product_Conversion is equal to the product of the partial
            --  conversion of X until J, and the partial conversion of Y
            --  until K.
         end loop;

         Array_Step_J_To_Next (Product_Conversion, X, Y, J);
         --  To prove first loop invariant

         pragma Assert (Product_Conversion
                        = Old_X * (+Y)
                        + (+X (J)) * Conversion_Array (J)
                        * Partial_Conversion (Y, 9));
         pragma Assert (Partial_Conversion (Y, 9) = (+Y));
         --  To prove third loop invariant

         pragma Loop_Invariant (Product_Conversion
                                = Partial_Conversion (Array_Step_J (X, Y, J), J + 9));
         --  At the end of this loop, will prove that Product_Conversion is
         --  equal to (+Final_Array).

         pragma Loop_Invariant (X_Conversion
                                = Partial_Conversion (X, J));

         pragma Loop_Invariant (Product_Conversion
                                = X_Conversion * (+Y));
         --  Distributivity of multiplication over addition.
      end loop;

      pragma Assert ((+X) = Partial_Conversion (X, 9));
      pragma Assert (Product_Conversion = Partial_Conversion (Array_Step_J (X, Y, 9), 18));
   end Prove_Multiply;

   -------------------
   -- Split_Product --
   -------------------

   procedure Split_Product
     (Old_Product, Old_X, Product_Conversion : Big_Integer;
      X, Y                                   : Integer_255;
      J, K                                   : Index_Type)
   is
   begin
      if J mod 2 = 1 and then K mod 2 = 1 then
         pragma Assert (Product_Conversion
                        = Old_Product
                        + (+X (J)) * (+Y (K))
                        * Conversion_Array (J + K) * (+2));
         pragma Assert ((+2) * Conversion_Array (J + K)
                        = Conversion_Array (J) * Conversion_Array (K));
         --  Case where Conversion_Array (J + K) * 2
         --             = Conversion_Array (J) * Conversion_Array (K).
      else
         pragma Assert (Conversion_Array (J + K)
                        = Conversion_Array (J) * Conversion_Array (K));
         --  Other case
      end if;

        if K > 0 then
           pragma Assert (Partial_Conversion (Y, K)
                          = Partial_Conversion (Y, K - 1)
                          + (+Y (K)) * Conversion_Array (K));
         --  Definition of Partial_Conversion, needed for proof
      end if;
   end Split_Product;
end Multiply_Proof;
