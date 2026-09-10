// Lean compiler output
// Module: KirovDolbeault.HodgeBridgeProbe
// Imports: public import Init public meta import Init public import KirovDolbeault.TraceResidue
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_PortTest_Jacobians_Dolbeault_puncturedHolomorphicSubmodule(lean_object*);
LEAN_EXPORT lean_object* lp_PortTest_Jacobians_Dolbeault_puncturedHolomorphicSubmodule___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_PortTest_Jacobians_Dolbeault_puncturedHolomorphicSubmodule(lean_object* v_c_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_PortTest_Jacobians_Dolbeault_puncturedHolomorphicSubmodule___boxed(lean_object* v_c_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_PortTest_Jacobians_Dolbeault_puncturedHolomorphicSubmodule(v_c_3_);
lean_dec_ref(v_c_3_);
return v_res_4_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_PortTest_KirovDolbeault_TraceResidue(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_PortTest_KirovDolbeault_TraceResidue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PortTest_KirovDolbeault_TraceResidue(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PortTest_KirovDolbeault_TraceResidue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_PortTest_KirovDolbeault_HodgeBridgeProbe(builtin);
}
#ifdef __cplusplus
}
#endif
