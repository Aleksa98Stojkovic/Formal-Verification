library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity Generic_LUT is
    Generic(init : std_logic_vector(15 downto 0) := std_logic_vector(to_unsigned(12, 16)));
    Port(a_i : in std_logic_vector(3 downto 0);
         b_o : out std_logic);
end Generic_LUT;

architecture Behavioral of Generic_LUT is
begin

b_o <= init(to_integer(unsigned(a_i)));

end Behavioral;
