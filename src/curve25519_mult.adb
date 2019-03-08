with Multiply_Proof; use Multiply_Proof;

package body Curve25519_Mult with
  SPARK_Mode
is

   function Multiply (X, Y : Integer_256) return Product_Integer is
      Product : Product_Integer := (others => 0);
      Aux : Long_Long_Integer;
   begin
      for J in Extended_Index_Type range 0 .. 9 loop
         for K in Extended_Index_Type range 0 .. 9 loop
            pragma Assert (X (J) in Min_Multiply .. Max_Multiply
                             and then Y (K) in Min_Multiply .. Max_Multiply);
            pragma Assert (X (J) * Y (K) in - (2**27 - 1)**2 .. (2**27 - 1)**2);
            Aux := X (J) * Y (K) * (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1);
            pragma Assert (Aux = X (J) * Y (K) * (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1));
            pragma Assert (Aux in (-2) * (2**27 - 1)**2 .. 2 * (2**27 - 1)**2);
            Product (J + K) := Product (J + K) + Aux;

            Partial_Product_Def (X, Y, J, K);

            if K /= Index_Type'Min (9, J + K) then
               pragma Assert (Product (J + K) = Partial_Product (X, Y, J - 1, K + 1) + Aux);
               pragma Assert (Product (J + K) = Partial_Product (X, Y, J, K));
            else
              pragma Assert (Product (J + K) = Aux);
              pragma Assert (Product (J + K) = Partial_Product (X, Y, J, K));
            end if;



            pragma Assert (Product (J + K) in
                             (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                           ..
                             2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

            pragma Loop_Invariant ((for all L in 0 .. J - 1 =>
                                      Product (L) = Product'Loop_Entry (L))
                                   and then
                                     (for all L in J + K + 1 .. 18 =>
                                        Product (L) = Product'Loop_Entry (L)));

            pragma Loop_Invariant (for all L in J .. J + K =>
                                     Product (L) in
                                     (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                                   ..
                                     2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

            pragma Loop_Invariant (for all L in J .. J + K =>
                                     Product (L) = Partial_Product (X, Y, J, L - J));

         end loop;

         pragma Assert (for all K in 0 .. J - 1 => Product (K) = Step_J (X, Y, J) (K));
         pragma Assert (Partial_Product (X, Y, J, 0) = Partial_Product (X, Y, J));

         pragma Loop_Invariant (for all L in J + 10 .. 18 =>
                                  Product (L) = Product'Loop_Entry (L));

         pragma Loop_Invariant (for all L in Extended_Index_Type range 0 .. 18 =>
                                  Product (L) in
                                  (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                                ..
                                  2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

         pragma Loop_Invariant (for all K in 0 .. J + 9 =>
                                  Product (K) = Step_J (X, Y, J) (K));

      end loop;

      pragma Assert (for all K in Product_Index_Type range 0 .. 18 =>
                       Product (K) = Step_J (X, Y, 9) (K));
      pragma Assert (Product = Final_Array (X, Y));

      Prove_Multiply (X, Y, Product);

      return Product;
   end Multiply;
end Curve25519_Mult;
