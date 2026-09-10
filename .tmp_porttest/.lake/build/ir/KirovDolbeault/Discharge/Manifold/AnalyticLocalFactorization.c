// Lean compiler output
// Module: KirovDolbeault.Discharge.Manifold.AnalyticLocalFactorization
// Imports: public import Init public meta import Init public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic public import Mathlib.Analysis.Analytic.Order public import Mathlib.Analysis.Analytic.IsolatedZeros public import Mathlib.Analysis.Analytic.Constructions public import Mathlib.Analysis.Calculus.FDeriv.Analytic
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
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Analytic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_Order(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_Constructions(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Analytic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_Discharge_Manifold_AnalyticLocalFactorization(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_Constructions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
