// REQUIRED_ARGS: -de
/* TEST_OUTPUT:
---
---
*/

struct BitArray
{
    BitArray opCom()
    {
        return BitArray();
    }
}

void main()
{
    BitArray ar;
    ar = ~ar;
}
