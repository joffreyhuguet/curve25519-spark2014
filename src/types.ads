with Big_Integers; use Big_Integers;

package Types with
  SPARK_Mode
is

   type Extended_Index_Type is new Integer range - 1 .. 9;
   subtype Index_Type is Extended_Index_Type range 0 .. 9;

   type Ints is array (Index_Type range <>) of Long_Long_Integer;
   subtype Ints_256 is Ints (0 .. 9) with
     Dynamic_Predicate => (for all J of Ints_256 => J in -2**31 .. 2**31 - 1);

   type Big_Ints is array (Index_Type) of Big_Integer;
   function Two_Power (Expon : Natural) return Big_Integer is
      (To_Big_Integer (Integer (2)) ** Expon);
   Conversion_Array : constant Big_Ints := (Two_Power (0),   Two_Power (26),
                                            Two_Power (51),  Two_Power (77),
                                            Two_Power (102), Two_Power (128),
                                            Two_Power (153), Two_Power (179),
                                            Two_Power (204), Two_Power (230));
end Types;
