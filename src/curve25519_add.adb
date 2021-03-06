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

package body Curve25519_Add with
  SPARK_Mode
is
   function Add (X, Y : Integer_255) return Integer_255 is
      Sum : Integer_255 := (others => 0);
      procedure Prove_Add with
        Ghost,
        Pre  => (for all J in Sum'Range => Sum (J) = X (J) + Y (J)),
        Post => To_Big_Integer (Sum) = To_Big_Integer (X) + To_Big_Integer (Y)
      is
        X_255, Y_255, Sum_255 : Big_Integer := Zero;
      begin
         for J in Sum'Range loop

            X_255 := X_255 + (+X (J)) * Conversion_Array (J);
            pragma Assert (X_255 = Partial_Conversion (X, J));

            Y_255 := Y_255 + (+Y (J)) * Conversion_Array (J);
            pragma Assert (Y_255 = Partial_Conversion (Y, J));

            Sum_255 := Sum_255 + (+Sum (J)) * Conversion_Array (J);
            pragma Assert (Sum_255 = Partial_Conversion (Sum, J));

            pragma Loop_Invariant (X_255 = Partial_Conversion (X, J));
            pragma Loop_Invariant (Y_255 = Partial_Conversion (Y, J));
            pragma Loop_Invariant (Sum_255 = Partial_Conversion (Sum, J));
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
end Curve25519_Add;
