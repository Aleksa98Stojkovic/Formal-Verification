library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity lut3 is
 generic(INIT : std_logic_vector(7 downto 0));
 port(
     I2 : in std_logic;
     I1 : in std_logic;
     I0 : in std_logic;
     O : out std_logic
 );

end lut3;

architecture rtl of lut3 is

signal input : std_logic_vector(2 downto 0);

begin

LUT3_proc : process(input)
 begin
     case input is
         when "000" => O <= INIT(0);
         when "001" => O <= INIT(1);
         when "010" => O <= INIT(2);
         when "011" => O <= INIT(3);
         when "100" => O <= INIT(4);
         when "101" => O <= INIT(5);
         when "110" => O <= INIT(6);
         when others => O <= INIT(7);
     end case;
 end process LUT3_proc;
 
 input <= I2 & I1 & I0;

end rtl;
