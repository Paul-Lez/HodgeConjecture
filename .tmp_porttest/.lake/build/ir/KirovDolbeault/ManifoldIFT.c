// Lean compiler output
// Module: KirovDolbeault.ManifoldIFT
// Imports: public import Init public meta import Init public import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic public import Mathlib.Geometry.Manifold.ContMDiff.Atlas public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
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
lean_object* initialize_PortTest_KirovDolbeault_Discharge_Manifold_ContMDiffOmegaAnalytic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiff_Atlas(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiff_NormedSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_InverseFunctionTheorem_Deriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_InverseFunctionTheorem_Analytic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_ManifoldIFT(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PortTest_KirovDolbeault_Discharge_Manifold_ContMDiffOmegaAnalytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiff_Atlas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiff_NormedSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_InverseFunctionTheorem_Deriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_InverseFunctionTheorem_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
