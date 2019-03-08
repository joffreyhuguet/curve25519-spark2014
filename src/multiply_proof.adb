package body Multiply_Proof with
  SPARK_Mode
is
   function Step_J (X, Y : Integer_256; J : Index_Type) return Integer_Curve25519 is
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
   end Step_J;

   procedure Prove_LI (Old_Product, Old_X, Product_BI : Big_Integer; X, Y : Integer_256; J, K : Index_Type) is
   begin
      Conversion_Array_Lemma (J, K);
      if J mod 2 = 1 and then K mod 2 = 1 then
         pragma Assert (Product_BI = Old_Product + (+X (J)) * Conversion_Array (J + K) * (+Y (K)) * (+2));
         pragma Assert ((+2) * Conversion_Array (J + K) = Conversion_Array (J) * Conversion_Array (K));
         pragma Assert ((+2) * Conversion_Array (J + K) * (+X (J)) * (+Y (K))
                        = Conversion_Array (J) * Conversion_Array (K) * (+X (J)) * (+Y (K)));
         pragma Assert (PRoduct_BI = Old_Product + Conversion_Array (J) * Conversion_Array (K) * (+X (J)) * (+Y (K)));
      else
         pragma Assert (Conversion_Array (J + K) = Conversion_Array (J) * Conversion_Array (K));
         pragma Assert (Conversion_Array (J + K) * (+X (J)) * (+Y (K))
                        = Conversion_Array (J) * Conversion_Array (K) * (+X (J)) * (+Y (K)));
         pragma Assert (Product_BI = Old_Product + (+X (J)) * Conversion_Array (J) * (+Y (K)) * Conversion_Array (K));
      end if;

      if K > 0 then
         pragma Assert (Partial_Conversion (Y, K - 1) + (+Y (K)) * Conversion_Array (K) = Partial_COnversion (Y, K));
         pragma Assert (Product_BI = Old_X * To_Integer_256 (Y)
                        + (+X (J)) * Conversion_Array (J)
                        * Partial_Conversion (Y, K));
      else
         pragma Assert (Partial_Conversion (Y, 0) = (+Y (0)) * Conversion_Array (0));
         pragma Assert (Product_BI = Old_X * To_Integer_256 (Y)
                        + (+X (J)) * Conversion_Array (J)
                        * Partial_Conversion (Y, K));
      end if;
   end Prove_LI;

   procedure First_Step (Product_BI : Big_Integer; X, Y : Integer_256) is
      Conversion, Previous : Big_Integer := Zero;
   begin
      for K in Index_Type range 0 .. 9 loop
         Previous := Conversion;
         Conversion := Conversion
           + (+X (0) * Y (K))
           * Conversion_Array (K);
         Diff_J_Def (X, Y, 0, K);

         if K > 0 then
            pragma Assert (Diff_J (X, Y, 0, K)
                           = Diff_J (X, Y, 0, K - 1)
                           + (+X (0) * Y (K))
                           * Conversion_Array (K));
            pragma Assert (Partial_Conversion (Step_J (X, Y, 0), K)
                           = Partial_Conversion (Step_J (X, Y, 0), K - 1)
                           + (+Step_J (X, Y, 0) (K)) * Conversion_Array (K));
            Partial_Product_Def (X, Y, 0, K);
            pragma Assert (Step_J (X, Y, 0) (K) = Partial_Product (X, Y, 0, K));
            pragma Assert (Partial_Product (X, Y, 0, K) = X (0) * Y (K));
         else
            pragma Assert (Diff_J (X, Y, 0, 0) = (+X (0) * Y (0))
                           * Conversion_Array (0));
         end if;

         pragma Loop_Invariant (Conversion = Diff_J (X, Y, 0, K));
         pragma Loop_Invariant (Conversion = Partial_Conversion (Step_J (X, Y, 0), K));
      end loop;
   end First_Step;


   procedure Prove_First_LI (Previous, Conversion : Big_Integer; X, Y : Integer_256; J, K : Index_Type) is
   begin
      Partial_Product_Def (X, Y, J, K);
      pragma Assert (Conversion
                     = Partial_Conversion (Step_J (X, Y, J), J + K - 1)
                     + (+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K));
   end Prove_First_LI;


   procedure Prove_Second_LI (Previous, Conversion : Big_Integer; X, Y : Integer_256; J, K : Index_Type) is
   begin
      pragma Assert (Partial_Product (X, Y, J) = Partial_Product (X, Y, J, 0));
      pragma Assert (Step_J (X, Y, J) (J + K) = Partial_Product (X, Y, J, K));
      Partial_Product_Def (X, Y, J, K);
      pragma Assert (Step_J (X, Y, J - 1) (J + K) = Partial_Product (X, Y, J - 1, K + 1));
      pragma Assert (X (J) in Min_Multiply .. Max_Multiply and then Y (J) in Min_Multiply .. Max_Multiply);
      pragma Assert (Step_J (X, Y, J) (J + K)
                     = Step_J (X, Y, J - 1) (J + K)
                     + (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K));
      Diff_J_Def (X, Y, J, K);
      if K > 0 then
         pragma Assert (Diff_J (X, Y, J, K)
                        = Diff_J (X, Y, J, K - 1)
                        + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (K))
                        * Conversion_Array (J + K));
         pragma Assert ((+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K)
                        = (+Step_J (X, Y, J - 1) (J + K)) * Conversion_Array (J + K)
                        + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
                        * (+X (J) * Y (K))
                        * Conversion_Array (J + K));
      else
         pragma Assert (Diff_J (X, Y, J, 0)
                        = (+X (J) * Y (0)) * Conversion_Array (J));
         pragma Assert ((+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K)
                        = (+Step_J (X, Y, J - 1) (J + K)) * Conversion_Array (J + K)
                        + (+X (J) * Y (0))
                        * Conversion_Array (J));
      end if;

   end Prove_Second_LI;

   procedure Step_Up (Product_BI : Big_Integer; X, Y : Integer_256; J : Index_Type) is
      Conversion, Previous : Big_Integer := Partial_Conversion (Step_J (X, Y, J), J - 1);
   begin
      Equal_To_Conversion (Step_J (X, Y, J), Step_J (X, Y, J - 1), J - 1);
      pragma Assert (Partial_Conversion (Step_J (X, Y, J), J - 1)
                     = Partial_Conversion (Step_J (X, Y, J - 1), J - 1));
      for K in Index_Type range 0 .. 9 loop
         Previous := Conversion;
         Conversion := Conversion + (+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K);
         Prove_First_LI (Previous, Conversion, X, Y, J, K);
         if K < 9 then
            Prove_Second_LI (Previous, Conversion, X, Y, J, K);
         else
            Partial_Product_Def (X, Y, J, 9);
            Diff_J_Def (X, Y, J, 9);
            pragma Assert (Previous = Partial_Conversion (Step_J (X, Y, J - 1), J + 8) + Diff_J (X, Y, J, 8));
            pragma Assert (Step_J (X, Y, J) (J + 9) = Partial_Product (X, Y, J, 9));
            pragma Assert (Partial_Product (X, Y, J, 9) = (if J mod 2 = 1 then 2 else 1) * X (J) * Y (9));
            pragma Assert (Diff_J (X, Y, J, 9)
                           = Diff_J (X, Y, J, 8)
                           + (+(if J mod 2 = 1 and then 9 mod 2 = 1 then 2 else 1))
                           * (+X (J) * Y (9))
                           * Conversion_Array (J + 9));
         end if;
         pragma Loop_Invariant (Conversion = Partial_Conversion (Step_J (X, Y, J), J + K));
         pragma Loop_Invariant (if K < 9 then Conversion = Partial_Conversion (Step_J (X, Y, J - 1), J + K)
                                + Diff_J (X, Y, J, K));
         pragma Loop_Invariant (if K = 9 then Conversion = Partial_Conversion (Step_J (X, Y, J - 1), J + 8)
                                + Diff_J (X, Y, J, 9));
      end loop;

   end Step_Up;

   procedure Prove_Multiply (X, Y : Integer_256; Product : Product_Integer) is
      X_256, Product_BI : Big_Integer := Zero;
      Old_X, Old_Product : Big_Integer;
   begin
      for J in Index_Type range 0 .. 9 loop
         Old_X := X_256;
         X_256 := X_256 + (+X (J)) * Conversion_Array (J);
         for K in Index_Type range 0 .. 9 loop
            Old_Product := Product_BI;
            pragma Assert (if K = 0 then
                              Old_Product = Old_X * To_Integer_256 (Y)
                           else Old_Product = Old_X * To_Integer_256 (Y)
                           + (+X (J)) * Conversion_Array (J)
                           * Partial_Conversion (Y, K - 1));
            Product_BI := Add_Next_BI (Product_BI, X, Y, J, K);

            Prove_LI (Old_Product, Old_X, Product_BI, X, Y, J, K);

            Diff_J_Def (X, Y, J, K);
            pragma Assert (Old_Product = PRoduct_BI'Loop_Entry + (if K > 0 then Diff_J (X, Y, J, K - 1) else Zero));
            pragma Loop_Invariant (Product_BI = Product_BI'Loop_Entry + Diff_J (X, Y, J, K));
            pragma Loop_Invariant (Product_BI
                                   = Old_X * To_Integer_256 (Y)
                                   + (+X (J)) * Conversion_Array (J)
                                   * Partial_Conversion (Y, K));
         end loop;

         pragma Assert (Product_BI
                        = Old_X * To_Integer_256 (Y)
                        + (+X (J)) * Conversion_Array (J)
                        * Partial_Conversion (Y, 9));
         pragma Assert (Partial_Conversion (Y, 9) = To_Integer_256 (Y));
         pragma Assert (Product_BI
                        = (Old_X + (+X (J))
                          * Conversion_Array (J)) * To_Integer_256 (Y));

         if J = 0 then
            First_Step (PRoduct_BI, X, Y);
         else
            Step_Up (Product_BI, X, Y, J);
         end if;

         pragma Loop_Invariant (Product_BI = Partial_Conversion (Step_J (X, Y, J), J + 9));
         pragma Loop_Invariant (X_256 = Partial_Conversion (X, J));
         pragma Loop_Invariant (Product_BI = X_256 * To_Integer_256 (Y));
      end loop;

      pragma Assert (Product_BI = Partial_Conversion (Step_J (X, Y, 9), 18));
      Equal_To_Conversion (Product, Step_J (X, Y, 9), 18);
      pragma Assert (Partial_Conversion (Step_J (X, Y, 9), 18) = Partial_Conversion (Product, 18));
      pragma Assert (Product_BI = Partial_Conversion (Product, 18));
      pragma Assert (Partial_Conversion (Product, 18) = To_Integer_Mult (Product));
      pragma Assert (Product_BI = To_Integer_Mult (Product));
      pragma Assert (Product_BI = Partial_Conversion (X, 9) * To_Integer_256 (Y));
      pragma Assert (Partial_Conversion (X, 9) = To_Integer_256 (X));
      pragma Assert (To_Integer_Mult (Product) = To_Integer_256 (X) * To_Integer_256 (Y));
   end Prove_Multiply;
end Multiply_Proof;
