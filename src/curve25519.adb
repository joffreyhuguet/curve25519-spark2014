--  Copyright 2008, Google Inc. All rights reserved.
--
--  Redistribution and use in source and binary forms, with or without
--  modification, are permitted provided that the following conditions are
--  met:
--
--  *  Redistributions of source code must retain the above copyright
--     notice, this list of conditions and the following disclaimer.
--  *  Redistributions in binary form must reproduce the above copyright
--     notice, this list of conditions and the following disclaimer in the
--     documentation and/or other materials provided with the distribution.
--  *  Neither the name of Google Inc. nor the names of its contributors may
--     be used to endorse or promote products derived from this software
--     without specific prior written permission.
--
--  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
--  IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
--  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
--  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
--  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
--  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
--  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
--  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
--  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
--  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
--  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

with Partial_Product_Impl_2; use Partial_Product_Impl_2;

package body Curve25519 with
  SPARK_Mode
is

   function Add (X, Y : Ints_256) return Ints_256 is
      Sum : Ints_256 := (others => 0);
      procedure Prove_Add with
        Ghost,
        Pre  => (for all J in Sum'Range => Sum (J) = X (J) + Y (J)),
        Post => To_Integer_256 (Sum) = To_Integer_256 (X) + To_Integer_256 (Y)
      is
        X_256, Y_256, Sum_256 : Big_Integer := Zero;
      begin
         for J in Sum'Range loop

            X_256 := X_256 + To_Big_Integer (X (J)) * Conversion_Array (J);
            Y_256 := Y_256 + To_Big_Integer (Y (J)) * Conversion_Array (J);
            Sum_256 := Sum_256 + To_Big_Integer (Sum (J)) * Conversion_Array (J);

            pragma Assert (To_Big_Integer (X (J)) * Conversion_Array (J) +
                             To_Big_Integer (Y (J)) * Conversion_Array (J) =
                           (To_Big_Integer (X (J) + Y (J))) * Conversion_Array (J));
            pragma Assert (X (J) + Y (J) = Sum (J));
            pragma Assert ((To_Big_Integer (X (J) + Y (J))) * Conversion_Array (J)
                           = To_Big_Integer (Sum (J)) * Conversion_Array (J));

            pragma Loop_Invariant (X_256 = Partial_Conversion (X, J));
            pragma Loop_Invariant (Y_256 = Partial_Conversion (Y, J));
            pragma Loop_Invariant (Sum_256 = Partial_Conversion (Sum, J));
            pragma Loop_Invariant (Partial_Conversion (Sum, J) =
                                     Partial_Conversion (X, J) +
                                     Partial_Conversion (Y, J));
         end loop;
      end Prove_Add;

   begin
      for J in Sum'Range loop
         Sum (J) := X (J) + Y (J);

         pragma Loop_Invariant (for all K in 0 .. J =>
                                  Sum (K) = X (K) + Y (K));
      end loop;
      Prove_Add;
      return Sum;
   end Add;

--  Multiply has 3 different implementations as for now. Every implementation
--  will be kept until the function is proved for one of these.
   function Multiply (X, Y : Ints_256) return Ints_Mult is
      Product : Ints_Mult := (others => 0);
      Aux : Long_Long_Integer;
      K_First, K_Last : Extended_Index_Type;
   begin

--  Implementation based on curve25519-donna implementation

--              Product (0)  :=      X (0) * Y (0);
--              Product (1)  :=      X (0) * Y (1) +
--                                   X (1) * Y (0);
--              Product (2)  := 2 *  X (1) * Y (1) +
--                                   X (0) * Y (2) +
--                                   X (2) * Y (0);
--              Product (3)  :=      X (1) * Y (2) +
--                                   X (2) * Y (1) +
--                                   X (0) * Y (3) +
--                                   X (3) * Y (0);
--              Product (4)  :=      X (2) * Y (2) +
--                              2 * (X (1) * Y (3) +
--                                   X (3) * Y (1)) +
--                                   X (0) * Y (4) +
--                                   X (4) * Y (0);
--              Product (5)  :=      X (2) * Y (3) +
--                                   X (3) * Y (2) +
--                                   X (1) * Y (4) +
--                                   X (4) * Y (1) +
--                                   X (0) * Y (5) +
--                                   X (5) * Y (0);
--              Product (6)  := 2 * (X (3) * Y (3) +
--                                   X (1) * Y (5) +
--                                   X (5) * Y (1)) +
--                                   X (2) * Y (4) +
--                                   X (4) * Y (2) +
--                                   X (0) * Y (6) +
--                                   X (6) * Y (0);
--              Product (7)  :=      X (3) * Y (4) +
--                                   X (4) * Y (3) +
--                                   X (2) * Y (5) +
--                                   X (5) * Y (2) +
--                                   X (1) * Y (6) +
--                                   X (6) * Y (1) +
--                                   X (0) * Y (7) +
--                                   X (7) * Y (0);
--              Product (8)  :=      X (4) * Y (4) +
--                              2 * (X (3) * Y (5) +
--                                   X (5) * Y (3) +
--                                   X (1) * Y (7) +
--                                   X (7) * Y (1)) +
--                                   X (2) * Y (6) +
--                                   X (6) * Y (2) +
--                                   X (0) * Y (8) +
--                                   X (8) * Y (0);
--              Product (9)  :=      X (4) * Y (5) +
--                                   X (5) * Y (4) +
--                                   X (3) * Y (6) +
--                                   X (6) * Y (3) +
--                                   X (2) * Y (7) +
--                                   X (7) * Y (2) +
--                                   X (1) * Y (8) +
--                                   X (8) * Y (1) +
--                                   X (0) * Y (9) +
--                                   X (9) * Y (0);
--              Product (10) := 2 * (X (5) * Y (5) +
--                                   X (3) * Y (7) +
--                                   X (7) * Y (3) +
--                                   X (1) * Y (9) +
--                                   X (9) * Y (1)) +
--                                   X (4) * Y (6) +
--                                   X (6) * Y (4) +
--                                   X (2) * Y (8) +
--                                   X (8) * Y (2);
--              Product (11) :=      X (5) * Y (6) +
--                                   X (6) * Y (5) +
--                                   X (4) * Y (7) +
--                                   X (7) * Y (4) +
--                                   X (3) * Y (8) +
--                                   X (8) * Y (3) +
--                                   X (2) * Y (9) +
--                                   X (9) * Y (2);
--              Product (12) :=      X (6) * Y (6) +
--                              2 * (X (5) * Y (7) +
--                                   X (7) * Y (5) +
--                                   X (3) * Y (9) +
--                                   X (9) * Y (3)) +
--                                   X (4) * Y (8) +
--                                   X (8) * Y (4);
--              Product (13) :=      X (6) * Y (7) +
--                                   X (7) * Y (6) +
--                                   X (5) * Y (8) +
--                                   X (8) * Y (5) +
--                                   X (4) * Y (9) +
--                                   X (9) * Y (4);
--              Product (14) := 2 * (X (7) * Y (7) +
--                                   X (5) * Y (9) +
--                                   X (9) * Y (5)) +
--                                   X (6) * Y (8) +
--                                   X (8) * Y (6);
--              Product (15) :=      X (7) * Y (8) +
--                                   X (8) * Y (7) +
--                                   X (6) * Y (9) +
--                                   X (9) * Y (6);
--              Product (16) :=      X (8) * Y (8) +
--                              2 * (X (7) * Y (9) +
--                                   X (9) * Y (7));
--              Product (17) :=      X (8) * Y (9) +
--                                   X (9) * Y (8);
--              Product (18) := 2 *  X (9) * Y (9);

--  Implementation 2

      for J in Extended_Index_Type range 0 .. 18 loop
         K_First := Extended_Index_Type'Max (J - 9, 0);
         K_Last := Extended_Index_Type'Min (J, 9);
         for K in K_First .. K_Last loop

            --  The following assertion should not be necessary because it is
            --  the definition of Partial_Product_Rec, but the provers cannot
            --  manage to prove it.

            pragma Assert (Partial_Product_Rec (X, Y, J, K) =
                           (if K = Extended_Index_Type'Max(J - 9, 0)
                              then (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K)
                           else
                                 Partial_Product_Rec (X, Y, J, K - 1) +
                              (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K)));

            pragma Assert (X (K) in - (2**27 - 1) .. 2**27 - 1
                           and then Y (J - K) in - (2**27 - 1) .. 2**27 - 1);
            Aux := (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K);
            pragma Assert (Aux in (-2) * (2**27 - 1)**2 .. 2 * (2**27 - 1)**2);

            if K = K_First then
               pragma Assert (Product (J) = 0);
            else
               pragma Assert (Product (J) = Partial_Product (X, Y, J, K - 1));
            end if;

            Product (J) := Product (J) + Aux;

            if K = K_First then
               pragma Assert (Product (J) = (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K));
            else
               pragma Assert (Product (J) = Partial_Product (X, Y, J, K - 1) +
                              (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K));
            end if;

            pragma Loop_Invariant (Product (J) in
                                     (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2
                                     ..
                                     2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2);
            pragma Loop_Invariant (Product (J) = Partial_Product (X, Y, J, K));
         end loop;
         pragma Loop_Invariant (for all K in 0 .. J => Product (K) = Partial_Product (X, Y, K));
      end loop;

--  Implementation 3

--        for J in Extended_Index_Type range 0 .. 9 loop
--           for K in Extended_Index_Type range 0 .. 9 loop
--
--              pragma Assert (X (J) in - (2**27 - 1) .. 2**27 - 1
--                             and then Y (K) in - (2**27 - 1) .. 2**27 - 1);
--              Aux := (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K);
--              pragma Assert (Aux in (-2) * (2**27 - 1)**2 .. 2 * (2**27 - 1)**2);
--              Product (J + K) := Product (J + K) + Aux;
--
--              pragma Loop_Invariant (for all L in J .. J + K =>
--                                       Product (L) in
--                                       (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
--                                     ..
--                                       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);
--              pragma Loop_Invariant (for all L in 0 .. J - 1 =>
--                                       Product (L) = Product'Loop_Entry (L));
--              pragma Loop_Invariant (for all L in J + K + 1 .. 18 =>
--                                       Product (L) = Product'Loop_Entry (L));
--           end loop;
--           pragma Loop_Invariant (for all L in Extended_Index_Type range 0 .. 18 =>
--                                    Product (L) in
--                                    (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
--                                  ..
--                                    2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);
--        end loop;

      return Product;
   end Multiply;
end Curve25519;
