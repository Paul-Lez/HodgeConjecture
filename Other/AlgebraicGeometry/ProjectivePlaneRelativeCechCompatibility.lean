import Other.AlgebraicGeometry.ProjectivePlaneRelativeCechClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology
open scoped AlgebraicGeometry
@[expose] noncomputable section
namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts
open AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))
set_option maxHeartbeats 600000

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneComplementRelativeTotalCompatibility :
    coordinateHyperplaneComplementToAmbientCechMap.f 2 ≫
        coordinateProjectiveCoverTotalFunctional +
      coordinateHyperplaneComplementCechTotal.d 2 1 ≫
        coordinateHyperplaneComplementFullFunctional = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [CategoryTheory.Limits.comp_zero]
  unfold coordinateHyperplaneComplementToAmbientCechMap
    rationalPullbackCoverNormalizedTotalMap
    rationalPullbackCoverNormalizedBicomplexMap
  rw [Preadditive.comp_add,
    HomologicalComplex₂.ιTotal_map_assoc]
  change _ +
    (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotal
        (ComplexShape.down ℕ) p q 2 hpq ≫
      ((coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).total
        (ComplexShape.down ℕ)).d 2 1 ≫
        coordinateHyperplaneComplementFullFunctional = 0
  have h2 :
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotal
          (ComplexShape.down ℕ) p q 2 hpq ≫
        ((coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).total
          (ComplexShape.down ℕ)).d 2 1 ≫ coordinateHyperplaneComplementFullFunctional =
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).d₁
          (ComplexShape.down ℕ) p q 1 ≫ coordinateHyperplaneComplementFullFunctional +
        (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).d₂
          (ComplexShape.down ℕ) p q 1 ≫ coordinateHyperplaneComplementFullFunctional := by
    rw [← Category.assoc,
      AlgebraicTopology.ιTotal_total_d
        (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono)
        p q 2 1 hpq,
      Preadditive.add_comp]
  rw [h2]
  have hpq' : p + q = 2 := hpq
  rcases p with _ | p
  · have hq : q = 2 := by omega
    subst q
    change _ ≫
      (coordinateHyperplaneAmbientCoverChainModels.cechComplex TupleClass.strictMono).ιTotal
        (ComplexShape.down ℕ) 0 2 2 hpq ≫ coordinateProjectiveCoverTotalFunctional + _ = 0
    rw [coordinateProjectiveCoverTotalFunctional_zero, comp_zero,
      AlgebraicTopology.d₁_zero,
      AlgebraicTopology.d₂_succ, Linear.units_smul_comp, Category.assoc,
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotalOrZero_eq
        (ComplexShape.down ℕ) 0 1 1 (by norm_num),
      coordinateHyperplaneComplementFullFunctional_singleton,
      coordinateHyperplaneComplementSingletonDegreeDesc_closed]
    simp
  rcases p with _ | p
  · have hq : q = 1 := by omega
    subst q
    change _ ≫
      (coordinateHyperplaneAmbientCoverChainModels.cechComplex TupleClass.strictMono).ιTotal
        (ComplexShape.down ℕ) 1 1 2 hpq ≫ coordinateProjectiveCoverTotalFunctional + _ = 0
    rw [coordinateProjectiveCoverTotalFunctional_pair,
      AlgebraicTopology.d₁_succ, Category.assoc,
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotalOrZero_eq
        (ComplexShape.down ℕ) 0 1 1 (by norm_num),
      coordinateHyperplaneComplementFullFunctional_singleton,
      AlgebraicTopology.d₂_succ, Linear.units_smul_comp, Category.assoc,
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotalOrZero_eq
        (ComplexShape.down ℕ) 1 0 1 (by norm_num),
      coordinateHyperplaneComplementFullFunctional_pair]
    apply (isColimitCofanMkObjOfIsColimit
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
      (fun a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport a.1))
      (fun a ↦ Sigma.ι
        (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
          coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a)
      (coproductIsCoproduct _)).hom_ext
    rintro ⟨a⟩
    dsimp only [SupportChainModels.Hom.cechMap, SupportChainModels.Hom.cechObjectMap]
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, Discrete.functor_obj]
    rw [← HomologicalComplex.eval_map]
    rw [Preadditive.comp_add]
    rw [← Category.assoc, ← Functor.map_comp, Limits.Sigma.ι_map]
    rw [HomologicalComplex.eval_map, HomologicalComplex.comp_f, Category.assoc]
    rw [rationalPullbackCoverLocalMap_app]
    have hpair :
        (Sigma.ι
          (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
            (rationalOpenCoverIntersectionChainModels
              ((𝟭 TopCat).obj coordinateHyperplaneSupportPair.right)
              projectiveCover).model (tupleSupport b.1)) a).f 1 ≫
          projectiveCoverPairDegreeDesc = projectiveCoverPairCochain a := by
      exact projectiveCoverPairDegreeDesc_ι a
    rw [hpair]
    rcases a with ⟨a, ha⟩
    rcases strictMono_finTwo_to_finThree_classify a ha with h01 | h02 | h12
    · subst a
      rw [projectiveCoverPairCochain]
      change (SSet.chainComplexMap (TopCat.toSSet.map
        (complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3))))
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair01Winding + _ = 0
      rw [projectiveCoverPair01Winding_restricts_complement]
      have houter := congrArg (fun f ↦ f.f 1)
        (coordinateHyperplaneComplementCoverChainModels_ι_comp_outer_d 0
          ⟨![0, 1], ha⟩)
      simp only [HomologicalComplex.comp_f] at houter
      change coordinateHyperplaneComplementAmbientPairWinding ⟨![0, 1], ha⟩ +
        (Sigma.ι
          (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
            coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
          ⟨![0, 1], ha⟩).f 1 ≫ _ = 0
      rw [Preadditive.comp_add]
      rw [← Category.assoc, houter]
      rw [Fin.sum_univ_two, HomologicalComplex.add_f_apply,
        HomologicalComplex.zsmul_f_apply, HomologicalComplex.zsmul_f_apply]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      norm_num
      dsimp only [coordinateHyperplaneComplementCoverChainModels] at *
      have hface1 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 0 (![0, 1] : Fin 2 → Fin 3)))
            (t := tupleSupport (![0, 1] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 0 (![0, 1] : Fin 2 → Fin 3) =
                  (![0, 1] : Fin 2 → Fin 3) ∘ (0 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (0 : Fin 2).succAbove (![0, 1] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 0 (![0, 1] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 1] : Fin 2 → Fin 3) 0 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc =
          (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair01ToSingletonOne)
            (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding := by
        rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
        rfl
      have hface0 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3)))
            (t := tupleSupport (![0, 1] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3) =
                  (![0, 1] : Fin 2 → Fin 3) ∘ (1 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (1 : Fin 2).succAbove (![0, 1] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 1] : Fin 2 → Fin 3) 1 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc = 0 := by
        rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
        have heq : Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3) =
            (![0] : Fin 1 → Fin 3) := by
          funext i
          fin_cases i
          rfl
        have hzero :
            coordinateHyperplaneComplementSingletonCochain
              ⟨Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 1] : Fin 2 → Fin 3) 1 ha⟩ = 0 := by
          have ha0 :
              (⟨Fin.removeNth 1 (![0, 1] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 1] : Fin 2 → Fin 3) 1 ha⟩ :
                {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a}) =
              ⟨![0], by decide⟩ := by
            apply Subtype.ext
            funext i
            fin_cases i
            rfl
          rw [ha0]
          simp [coordinateHyperplaneComplementSingletonCochain]
        rw [hzero, comp_zero]
      rw [hface1]
      rw [hface0]
      rw [coordinateHyperplaneComplementPairCorrectionDegreeDesc_vertical
        ⟨![0, 1], ha⟩]
      simp only [sub_zero, neg_zero, add_zero]
      have hvertical :
          (coordinateHyperplaneComplementCoverChainModels.model
            (tupleSupport (![0, 1] : Fin 2 → Fin 3))).d 1 0 ≫
            coordinateHyperplaneComplementPairCorrection ⟨![0, 1], ha⟩ =
          (ChernWinding.singularChains (TopCat.of (openCoverIntersection
            coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
            ({0, 1} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair01Correction := by
        rfl
      rw [hvertical]
      simpa [coordinateHyperplaneComplementAmbientPairWinding,
        coordinateHyperplaneComplementPairCorrection, sub_eq_add_neg, add_assoc] using
        (sub_eq_zero.mpr complementCoverPair01_face_localEquation)
    · subst a
      rw [projectiveCoverPairCochain]
      change (SSet.chainComplexMap (TopCat.toSSet.map
        (complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3))))
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair02Winding + _ = 0
      rw [projectiveCoverPair02Winding_restricts_complement]
      have houter := congrArg (fun f ↦ f.f 1)
        (coordinateHyperplaneComplementCoverChainModels_ι_comp_outer_d 0
          ⟨![0, 2], ha⟩)
      simp only [HomologicalComplex.comp_f] at houter
      dsimp only [coordinateHyperplaneComplementCoverChainModels] at *
      change coordinateHyperplaneComplementAmbientPairWinding ⟨![0, 2], ha⟩ +
        (Sigma.ι
          (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
            coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
          ⟨![0, 2], ha⟩).f 1 ≫ _ = 0
      rw [Preadditive.comp_add, ← Category.assoc, houter]
      rw [Fin.sum_univ_two, HomologicalComplex.add_f_apply,
        HomologicalComplex.zsmul_f_apply, HomologicalComplex.zsmul_f_apply]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      norm_num
      have hface2 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 0 (![0, 2] : Fin 2 → Fin 3)))
            (t := tupleSupport (![0, 2] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 0 (![0, 2] : Fin 2 → Fin 3) =
                  (![0, 2] : Fin 2 → Fin 3) ∘ (0 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (0 : Fin 2).succAbove (![0, 2] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 0 (![0, 2] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 2] : Fin 2 → Fin 3) 0 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc =
          (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair02ToSingletonTwo)
            (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding := by
        rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
        rfl
      have hface0 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3)))
            (t := tupleSupport (![0, 2] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3) =
                  (![0, 2] : Fin 2 → Fin 3) ∘ (1 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (1 : Fin 2).succAbove (![0, 2] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 2] : Fin 2 → Fin 3) 1 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc = 0 := by
        rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
        have heq : Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3) =
            (![0] : Fin 1 → Fin 3) := by
          funext i
          fin_cases i
          rfl
        have ha0 :
            (⟨Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3), by
              exact TupleClass.strictMono.removeNth_mem 0 (![0, 2] : Fin 2 → Fin 3) 1 ha⟩ :
              {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a}) =
            ⟨![0], by decide⟩ := by
          apply Subtype.ext
          funext i
          fin_cases i
          rfl
        have hzero :
            coordinateHyperplaneComplementSingletonCochain
              ⟨Fin.removeNth 1 (![0, 2] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![0, 2] : Fin 2 → Fin 3) 1 ha⟩ = 0 := by
          rw [ha0]
          simp [coordinateHyperplaneComplementSingletonCochain]
        rw [hzero, comp_zero]
      rw [hface2, hface0]
      rw [coordinateHyperplaneComplementPairCorrectionDegreeDesc_vertical
        ⟨![0, 2], ha⟩]
      simp only [sub_zero, neg_zero, add_zero]
      have hvertical :
          (coordinateHyperplaneComplementCoverChainModels.model
            (tupleSupport (![0, 2] : Fin 2 → Fin 3))).d 1 0 ≫
            coordinateHyperplaneComplementPairCorrection ⟨![0, 2], ha⟩ =
          (ChernWinding.singularChains (TopCat.of (openCoverIntersection
            coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
            ({0, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair02Correction := by
        rfl
      rw [hvertical]
      simpa [coordinateHyperplaneComplementAmbientPairWinding,
        coordinateHyperplaneComplementPairCorrection, sub_eq_add_neg, add_assoc] using
        (sub_eq_zero.mpr complementCoverPair02_face_localEquation)
    · subst a
      rw [projectiveCoverPairCochain]
      change (SSet.chainComplexMap (TopCat.toSSet.map
        (complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3))))
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair12Winding + _ = 0
      rw [projectiveCoverPair12Winding_restricts_complement]
      have houter := congrArg (fun f ↦ f.f 1)
        (coordinateHyperplaneComplementCoverChainModels_ι_comp_outer_d 0
          ⟨![1, 2], ha⟩)
      simp only [HomologicalComplex.comp_f] at houter
      dsimp only [coordinateHyperplaneComplementCoverChainModels] at *
      change coordinateHyperplaneComplementAmbientPairWinding ⟨![1, 2], ha⟩ +
        (Sigma.ι
          (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
            coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
          ⟨![1, 2], ha⟩).f 1 ≫ _ = 0
      rw [Preadditive.comp_add, ← Category.assoc, houter]
      rw [Fin.sum_univ_two, HomologicalComplex.add_f_apply,
        HomologicalComplex.zsmul_f_apply, HomologicalComplex.zsmul_f_apply]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      norm_num
      have hface2 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 0 (![1, 2] : Fin 2 → Fin 3)))
            (t := tupleSupport (![1, 2] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 0 (![1, 2] : Fin 2 → Fin 3) =
                  (![1, 2] : Fin 2 → Fin 3) ∘ (0 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (0 : Fin 2).succAbove (![1, 2] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 0 (![1, 2] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![1, 2] : Fin 2 → Fin 3) 0 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc =
          (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonTwo)
            (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding := by
        rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
        rfl
      have hface1 :
          ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
              coordinateHyperplaneComplementCover).face
            (s := tupleSupport (Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3)))
            (t := tupleSupport (![1, 2] : Fin 2 → Fin 3)) (by
              rw [tupleSupport_subset_iff]
              have heq : Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3) =
                  (![1, 2] : Fin 2 → Fin 3) ∘ (1 : Fin 2).succAbove := by
                funext i
                rw [Fin.removeNth_apply]
                rfl
              rw [heq]
              exact Set.range_comp_subset_range
                (1 : Fin 2).succAbove (![1, 2] : Fin 2 → Fin 3))).f 1 ≫
            (Sigma.ι
              (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                  coordinateHyperplaneComplementCover).model (tupleSupport b.1))
              ⟨Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3), by
                exact TupleClass.strictMono.removeNth_mem 0 (![1, 2] : Fin 2 → Fin 3) 1 ha⟩).f 1 ≫
            coordinateHyperplaneComplementSingletonDegreeDesc =
            (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonOne)
            (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding := by
        have h1 : Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3) =
            (![1] : Fin 1 → Fin 3) := by
          funext i
          fin_cases i
          rfl
        have haux : ∀ (a : Fin 1 → Fin 3)
            (ha : TupleClass.strictMono.mem 0 a)
            (hs : (tupleSupport a).1 ⊆ (tupleSupport (![1, 2] : Fin 2 → Fin 3)).1),
            a = (![1] : Fin 1 → Fin 3) →
            ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                coordinateHyperplaneComplementCover).face
              (s := tupleSupport a)
              (t := tupleSupport (![1, 2] : Fin 2 → Fin 3)) hs).f 1 ≫
              (Sigma.ι
                (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
                  (rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
                    coordinateHyperplaneComplementCover).model (tupleSupport b.1))
                ⟨a, ha⟩).f 1 ≫ coordinateHyperplaneComplementSingletonDegreeDesc =
            (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonOne)
              (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding := by
          intro a ha hs ha1
          subst a
          rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
          rfl
        apply haux
          (Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3))
          (by exact TupleClass.strictMono.removeNth_mem 0 (![1, 2] : Fin 2 → Fin 3) 1 ha)
          (by
            rw [tupleSupport_subset_iff]
            have heq : Fin.removeNth 1 (![1, 2] : Fin 2 → Fin 3) =
                (![1, 2] : Fin 2 → Fin 3) ∘ (1 : Fin 2).succAbove := by
              funext i
              rw [Fin.removeNth_apply]
              rfl
            rw [heq]
            exact Set.range_comp_subset_range
              (1 : Fin 2).succAbove (![1, 2] : Fin 2 → Fin 3))
          h1
      rw [hface2, hface1]
      rw [coordinateHyperplaneComplementPairCorrectionDegreeDesc_vertical
        ⟨![1, 2], ha⟩]
      simp only [sub_zero, neg_zero, add_zero]
      have hvertical :
          (coordinateHyperplaneComplementCoverChainModels.model
            (tupleSupport (![1, 2] : Fin 2 → Fin 3))).d 1 0 ≫
            coordinateHyperplaneComplementPairCorrection ⟨![1, 2], ha⟩ =
          (ChernWinding.singularChains (TopCat.of (openCoverIntersection
            coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
            ({1, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair12Correction := by
        rfl
      rw [hvertical]
      simpa [coordinateHyperplaneComplementAmbientPairWinding,
        coordinateHyperplaneComplementPairCorrection, sub_eq_add_neg, add_assoc] using
        (sub_eq_zero.mpr complementCoverPair12_face_localEquation)
  · have hq : q = 0 := by omega
    subst q
    have hp : p = 0 := by omega
    subst p
    change _ ≫
      (coordinateHyperplaneAmbientCoverChainModels.cechComplex TupleClass.strictMono).ιTotal
        (ComplexShape.down ℕ) 2 0 2 hpq ≫ coordinateProjectiveCoverTotalFunctional + _ = 0
    rw [coordinateProjectiveCoverTotalFunctional_triple,
      AlgebraicTopology.d₁_succ, Category.assoc,
      (coordinateHyperplaneComplementCoverChainModels.cechComplex TupleClass.strictMono).ιTotalOrZero_eq
        (ComplexShape.down ℕ) 1 0 1 (by norm_num),
      coordinateHyperplaneComplementFullFunctional_pair,
      AlgebraicTopology.d₂_zero, zero_comp]
    apply (isColimitCofanMkObjOfIsColimit
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0)
      (fun a : {a : Fin 3 → Fin 3 // TupleClass.strictMono.mem 2 a} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport a.1))
      (fun a ↦ Sigma.ι
        (fun b : {b : Fin 3 → Fin 3 // TupleClass.strictMono.mem 2 b} ↦
          coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a)
      (coproductIsCoproduct _)).hom_ext
    rintro ⟨a⟩
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, Discrete.functor_obj]
    rw [← HomologicalComplex.eval_map]
    dsimp only [SupportChainModels.Hom.cechMap, SupportChainModels.Hom.cechObjectMap]
    rw [Preadditive.comp_add]
    rw [← Functor.map_comp_assoc, Limits.Sigma.ι_map]
    rw [HomologicalComplex.eval_map, HomologicalComplex.comp_f, Category.assoc]
    rw [rationalPullbackCoverLocalMap_app]
    rcases a with ⟨a, ha⟩
    have htriple : a = ![0, 1, 2] := strictMono_finThree_eq_id a ha
    subst a
    have htripleDesc :
        (Sigma.ι
            (fun b : {b : Fin 3 → Fin 3 // TupleClass.strictMono.mem 2 b} ↦
              (rationalOpenCoverIntersectionChainModels
                ((𝟭 TopCat).obj coordinateHyperplaneSupportPair.right)
                projectiveCover).model (tupleSupport b.1))
            ⟨![0, 1, 2], ha⟩).f 0 ≫ projectiveCoverTripleDegreeDesc =
          projectiveCoverTripleCochain ⟨![0, 1, 2], ha⟩ := by
      exact projectiveCoverTripleDegreeDesc_ι ⟨![0, 1, 2], ha⟩
    rw [htripleDesc]
    have hrestrict :
        (SSet.chainComplexMap
          (TopCat.toSSet.map
            (pullbackOpenCoverIntersectionMap coordinateHyperplaneSupportPair.hom
              projectiveCover ↑(tupleSupport (![0, 1, 2] : Fin 3 → Fin 3))))
          (ModuleCat.of ℚ ℚ)).f 0 ≫
            projectiveCoverTripleCochain ⟨![0, 1, 2], ha⟩ =
          -complementCoverTripleDefectTuple := by
      have hc :
          projectiveCoverTripleCochain ⟨![0, 1, 2], ha⟩ =
            -projectiveCoverTripleDefectTuple := by
        simp [projectiveCoverTripleCochain]
      rw [hc, Preadditive.comp_neg]
      change -((SSet.chainComplexMap (TopCat.toSSet.map
        (complementCoverIntersectionToAmbientIntersection
          ({0, 1, 2} : Finset (Fin 3))))
        (ModuleCat.of ℚ ℚ)).f 0 ≫ projectiveCoverTripleDefect) =
          -complementCoverTripleDefectTuple
      rw [projectiveCoverTripleDefect_restricts_complement]
      rfl
    rw [hrestrict]
    simp only [add_zero]
    simpa [sub_eq_add_neg, add_comm] using
      coordinateHyperplaneComplementPairCorrection_outer_triple

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
