// Lean compiler output
// Module: KirovDolbeault.Dolbeault.RealForms
// Imports: public import Init public meta import Init public import KirovDolbeault.Dolbeault.RealManifold public import Mathlib.Geometry.Manifold.VectorBundle.Hom public import Mathlib.Geometry.Manifold.VectorBundle.Tangent public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection public import Mathlib.Analysis.Normed.Module.Basic public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
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
lean_object* initialize_PortTest_KirovDolbeault_Dolbeault_RealManifold(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_Hom(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_Tangent(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_ContMDiffSection(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiffMFDeriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_Algebra_SmoothFunctions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_Dolbeault_RealForms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PortTest_KirovDolbeault_Dolbeault_RealManifold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_Hom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_Tangent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_VectorBundle_ContMDiffSection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_ContMDiffMFDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_Algebra_SmoothFunctions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
