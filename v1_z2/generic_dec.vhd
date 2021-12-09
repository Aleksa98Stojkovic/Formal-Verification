library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use ieee.numeric_std.all;

entity generic_dec is
    Generic(width : natural := 2);
    Port(en_i : in std_logic;
         a_i : in std_logic_vector(width - 1 downto 0);
         b_o : out std_logic_vector(2 ** width - 1 downto 0));
end generic_dec;

architecture Behavioral of generic_dec is

begin

logic: process(en_i, a_i)
begin
    b_o <= (others => '0');
    if(en_i = '1') then
        b_o <= std_logic_vector(shift_left(to_unsigned(1, b_o'length), to_integer(unsigned(a_i)))); 
    end if;
end process;

end Behavioral;
