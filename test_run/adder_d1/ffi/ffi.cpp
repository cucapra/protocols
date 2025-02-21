
#include "verilated.h"
#include "Vadder_d1.h"

extern "C" {
    void* ffi_new_Vadder_d1() {
        return new Vadder_d1{};
    }

    
    void ffi_Vadder_d1_eval(Vadder_d1* top) {
        top->eval();
    }

    void ffi_delete_Vadder_d1(Vadder_d1* top) {
        delete top;
    }


    void ffi_Vadder_d1_pin_A(Vadder_d1* top, VL_IN(new_value, 31, 0)) {
        top->A = new_value;
    }
            

    void ffi_Vadder_d1_pin_B(Vadder_d1* top, VL_IN(new_value, 31, 0)) {
        top->B = new_value;
    }
            

    VL_OUT(/* return value */, 31, 0) ffi_Vadder_d1_read_S(Vadder_d1* top) {
        return top->S;
    }
            
} // extern "C"
