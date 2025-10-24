-- Greg Stitt
-- StittHub (www.stitt-hub.com)

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- Include to get initializer array.
use work.ram_init_demo_pkg.all;

entity ram_init_array_demo is
    generic (
        DATA_WIDTH  : positive := 8;
        ADDR_WIDTH  : positive := 6;
        REG_RD_DATA : boolean  := false;
        WRITE_FIRST : boolean  := false;
        STYLE       : string   := ""
        );
    port (
        clk     : in  std_logic;
        rd_en   : in  std_logic;
        rd_addr : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        rd_data : out std_logic_vector(DATA_WIDTH-1 downto 0);
        wr_en   : in  std_logic;
        wr_addr : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        wr_data : in  std_logic_vector(DATA_WIDTH-1 downto 0)
        );
end ram_init_array_demo;

architecture default_arch of ram_init_array_demo is

begin

    U_TOP : entity work.ram_sdp_init_array
        generic map (
            DATA_WIDTH  => DATA_WIDTH,
            ADDR_WIDTH  => ADDR_WIDTH,
            REG_RD_DATA => REG_RD_DATA,
            WRITE_FIRST => WRITE_FIRST,
            STYLE       => STYLE,
            INIT        => RAM_INIT_DEMO_ARRAY_SLV
            )
        port map (clk     => clk,
                  rd_en   => rd_en,
                  rd_addr => rd_addr,
                  rd_data => rd_data,
                  wr_en   => wr_en,
                  wr_addr => wr_addr,
                  wr_data => wr_data);

end architecture;
