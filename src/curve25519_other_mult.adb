with Partial_Product_Impl_2; use Partial_Product_Impl_2;

package body Curve25519_Other_Mult with
  SPARK_Mode
is

   --  Implementation based on curve25519-donna implementation

   function Multiply_1 (X, Y : Integer_256) return Product_Integer is
      Product : Product_Integer := (others => 0);
   begin

            Product (0)  :=      X (0) * Y (0);
            Product (1)  :=      X (0) * Y (1) +
                                 X (1) * Y (0);
            Product (2)  := 2 *  X (1) * Y (1) +
                                 X (0) * Y (2) +
                                 X (2) * Y (0);
            Product (3)  :=      X (1) * Y (2) +
                                 X (2) * Y (1) +
                                 X (0) * Y (3) +
                                 X (3) * Y (0);
            Product (4)  :=      X (2) * Y (2) +
                            2 * (X (1) * Y (3) +
                                 X (3) * Y (1)) +
                                 X (0) * Y (4) +
                                 X (4) * Y (0);
            Product (5)  :=      X (2) * Y (3) +
                                 X (3) * Y (2) +
                                 X (1) * Y (4) +
                                 X (4) * Y (1) +
                                 X (0) * Y (5) +
                                 X (5) * Y (0);
            Product (6)  := 2 * (X (3) * Y (3) +
                                 X (1) * Y (5) +
                                 X (5) * Y (1)) +
                                 X (2) * Y (4) +
                                 X (4) * Y (2) +
                                 X (0) * Y (6) +
                                 X (6) * Y (0);
            Product (7)  :=      X (3) * Y (4) +
                                 X (4) * Y (3) +
                                 X (2) * Y (5) +
                                 X (5) * Y (2) +
                                 X (1) * Y (6) +
                                 X (6) * Y (1) +
                                 X (0) * Y (7) +
                                 X (7) * Y (0);
            Product (8)  :=      X (4) * Y (4) +
                            2 * (X (3) * Y (5) +
                                 X (5) * Y (3) +
                                 X (1) * Y (7) +
                                 X (7) * Y (1)) +
                                 X (2) * Y (6) +
                                 X (6) * Y (2) +
                                 X (0) * Y (8) +
                                 X (8) * Y (0);
            Product (9)  :=      X (4) * Y (5) +
                                 X (5) * Y (4) +
                                 X (3) * Y (6) +
                                 X (6) * Y (3) +
                                 X (2) * Y (7) +
                                 X (7) * Y (2) +
                                 X (1) * Y (8) +
                                 X (8) * Y (1) +
                                 X (0) * Y (9) +
                                 X (9) * Y (0);
            Product (10) := 2 * (X (5) * Y (5) +
                                 X (3) * Y (7) +
                                 X (7) * Y (3) +
                                 X (1) * Y (9) +
                                 X (9) * Y (1)) +
                                 X (4) * Y (6) +
                                 X (6) * Y (4) +
                                 X (2) * Y (8) +
                                 X (8) * Y (2);
            Product (11) :=      X (5) * Y (6) +
                                 X (6) * Y (5) +
                                 X (4) * Y (7) +
                                 X (7) * Y (4) +
                                 X (3) * Y (8) +
                                 X (8) * Y (3) +
                                 X (2) * Y (9) +
                                 X (9) * Y (2);
            Product (12) :=      X (6) * Y (6) +
                            2 * (X (5) * Y (7) +
                                 X (7) * Y (5) +
                                 X (3) * Y (9) +
                                 X (9) * Y (3)) +
                                 X (4) * Y (8) +
                                 X (8) * Y (4);
            Product (13) :=      X (6) * Y (7) +
                                 X (7) * Y (6) +
                                 X (5) * Y (8) +
                                 X (8) * Y (5) +
                                 X (4) * Y (9) +
                                 X (9) * Y (4);
            Product (14) := 2 * (X (7) * Y (7) +
                                 X (5) * Y (9) +
                                 X (9) * Y (5)) +
                                 X (6) * Y (8) +
                                 X (8) * Y (6);
            Product (15) :=      X (7) * Y (8) +
                                 X (8) * Y (7) +
                                 X (6) * Y (9) +
                                 X (9) * Y (6);
            Product (16) :=      X (8) * Y (8) +
                            2 * (X (7) * Y (9) +
                                 X (9) * Y (7));
            Product (17) :=      X (8) * Y (9) +
                                 X (9) * Y (8);
            Product (18) := 2 *  X (9) * Y (9);

      return Product;

   end Multiply_1;

--  Implementation 2

   function Multiply_2 (X, Y : Integer_256) return Product_Integer is
      Product         : Product_Integer := (others => 0);
      Aux             : Long_Long_Integer;
      K_First, K_Last : Extended_Index_Type;
   begin
      for J in Extended_Index_Type range 0 .. 18 loop
         K_First := Extended_Index_Type'Max (J - 9, 0);
         K_Last := Extended_Index_Type'Min (J, 9);
         for K in K_First .. K_Last loop

            --  The following assertion should not be necessary because it is
            --  the definition of Partial_Product_Rec, but the provers cannot
            --  manage to prove it.

            Partial_Product_Def (X, Y, J, K);

            if K = K_First then
               pragma Assert (Product (J) = 0);
            else
               pragma Assert (Product (J) = Partial_Product (X, Y, J, K - 1));
            end if;

            pragma Assert (X (K) in - (2**27 - 1) .. 2**27 - 1
                           and then Y (J - K) in - (2**27 - 1) .. 2**27 - 1);
            Aux := (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K);
            pragma Assert (Aux in (-2) * (2**27 - 1)**2 .. 2 * (2**27 - 1)**2);
            Product (J) := Product (J) + Aux;

            if K = K_First then
               pragma Assert
                 (Product (J)
                  = (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K));
            else
               pragma Assert
                 (Product (J)
                  = Partial_Product (X, Y, J, K - 1)
                  + (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K));
            end if;

            pragma Loop_Invariant (Product (J) in
                                     (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2
                                   ..
                                     2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2);
          pragma Loop_Invariant (Product (J) = Partial_Product (X, Y, J, K));
         end loop;
       pragma Loop_Invariant (for all K in 0 .. J =>
                                Product (K) = Partial_Product (X, Y, K));
      end loop;
      return Product;
   end Multiply_2;
end Curve25519_Other_Mult;
