// Lean compiler output
// Module: KirovDolbeault.Discharge.Manifold.AnalyticFiberDiscrete
// Imports: public import Init public meta import Init public import KirovDolbeault.Discharge.Manifold.Degree public import Mathlib.Analysis.Analytic.IsolatedZeros public import Mathlib.Topology.DiscreteSubset
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PortTest_KirovDolbeault_Discharge_Manifold_Degree(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_DiscreteSubset(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_Discharge_Manifold_AnalyticFiberDiscrete(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PortTest_KirovDolbeault_Discharge_Manifold_Degree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_DiscreteSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
