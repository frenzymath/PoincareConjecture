import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CocycleHomologyEvaluation

set_option autoImplicit false

open Set CategoryTheory Limits
open scoped Topology Simplicial BigOperators Classical

universe u

namespace PoincareConjecture.M76.AntipodalCover

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (q : E → X) (τ : E ≃ₜ E)
  (hτ : Function.Involutive τ) (hne : ∀ z, τ z ≠ z)
  (hf : ∀ a b, q a = q b ↔ a = b ∨ a = τ b)
  (hq : IsCoveringMap q) (hs : Function.Surjective q)

noncomputable def representative (x : X) : E := (hs x).choose

theorem representative_proj (x : X) : q (representative q hs x) = x :=
  (hs x).choose_spec

noncomputable def sheet (z : E) : ZMod 2 :=
  if z = representative q hs (q z) then 0 else 1

include hf in
theorem proj_antipode (z : E) : q (τ z) = q z := (hf _ _).mpr (Or.inr rfl)

theorem sheet_representative (x : X) : sheet q hs (representative q hs x) = 0 := by
  simp [sheet, representative_proj]

include hτ hne hf in
theorem sheet_antipode (z : E) : sheet q hs (τ z) = sheet q hs z + 1 := by
  classical
  have hz := (hf z (representative q hs (q z))).mp
    (representative_proj q hs (q z)).symm
  rw [sheet, proj_antipode q τ hf, sheet]
  rcases hz with hz | hz
  · rw [if_pos hz, if_neg]
    · norm_num
    · intro he
      exact hne z (he.trans hz.symm)
  · have hn : z ≠ representative q hs (q z) := by
      intro he
      exact hne (representative q hs (q z)) (hz.symm.trans he)
    have ht : τ z = representative q hs (q z) :=
      (congrArg τ hz).trans (hτ _)
    rw [if_pos ht, if_neg hn]
    decide

noncomputable def pathValue {x y : X} (p : Path x y) : ZMod 2 :=
  sheet q hs (hq.liftPath p.toContinuousMap (representative q hs x)
    (p.source.trans (representative_proj q hs x).symm) 1)

include hτ hne hf in
theorem pathValue_of_lift {x y : X} (p : Path x y)
    {a b : E} (L : Path a b) (hL : ∀ t, q (L t) = p t) :
    pathValue q hq hs p = sheet q hs b - sheet q hs a := by
  classical
  have ha : q a = x := by simpa using hL 0
  have ha' := (hf a (representative q hs x)).mp
    (ha.trans (representative_proj q hs x).symm)
  rcases ha' with ha' | ha'
  · have heq : L.toContinuousMap = hq.liftPath p.toContinuousMap
        (representative q hs x) (p.source.trans (representative_proj q hs x).symm) :=
      (hq.eq_liftPath_iff' _).mpr ⟨funext hL, L.source.trans ha'⟩
    unfold pathValue
    rw [← heq]
    change sheet q hs (L 1) = _
    rw [L.target, ha', sheet_representative, sub_zero]
  · let M : C(unitInterval, E) := ⟨fun t => τ (L t), τ.continuous.comp L.continuous⟩
    have hM (t) : q (M t) = p t := (proj_antipode q τ hf _).trans (hL t)
    have hzero : M 0 = representative q hs x := by
      change τ (L 0) = _
      rw [L.source, ha', hτ]
    have heq : M = hq.liftPath p.toContinuousMap
        (representative q hs x) (p.source.trans (representative_proj q hs x).symm) :=
      (hq.eq_liftPath_iff' _).mpr ⟨funext hM, hzero⟩
    unfold pathValue
    rw [← heq]
    change sheet q hs (τ (L 1)) = _
    rw [L.target, sheet_antipode q τ hτ hne hf, ha',
      sheet_antipode q τ hτ hne hf, sheet_representative]
    norm_num only [zero_add]
    rw [sub_eq_add_neg, show -(1 : ZMod 2) = 1 by decide]

open CutGraph

noncomputable def singularValue
    (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) : ZMod 2 :=
  pathValue q hq hs (simplexEdgePath ((TopCat.of X).toSSetObjEquiv _ s))

include hτ hne hf in
theorem singularValue_pathSimplex {x y : X} (p : Path x y) :
    singularValue q hq hs (pathSimplex (X := TopCat.of X) p) =
      pathValue q hq hs p := by
  let L := hq.liftPath p.toContinuousMap (representative q hs x)
    (p.source.trans (representative_proj q hs x).symm)
  let LP : Path (representative q hs x) (L 1) :=
    ⟨L, hq.liftPath_zero _ _ _, rfl⟩
  let f := (TopCat.of X).toSSetObjEquiv _ (pathSimplex (X := TopCat.of X) p)
  have hL (t) : q (LP t) = simplexEdgePath f t := by
    change q (L t) = p (stdSimplexHomeomorphUnitInterval
      (stdSimplexHomeomorphUnitInterval.symm t))
    rw [Homeomorph.apply_symm_apply]
    exact congr_fun (hq.liftPath_lifts _ _ _) t
  exact (pathValue_of_lift q τ hτ hne hf hq hs (simplexEdgePath f) LP hL).trans
    (by rw [sheet_representative, sub_zero]; rfl)

include hτ hne hf in
theorem singularValue_cocycle (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌) :
    (∑ j : Fin 3, ((-1 : ℤ) ^ j.val) •
      singularValue q hq hs ((TopCat.toSSet.obj (TopCat.of X)).δ j s)) = 0 := by
  let f : C(stdSimplex ℝ (Fin 3), X) := (TopCat.of X).toSSetObjEquiv _ s
  let v : Fin 3 → stdSimplex ℝ (Fin 3) := stdSimplex.vertex
  let : ContractibleSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).contractibleSpace ⟨v 0, (v 0).property⟩
  let : LocallyPathConnectedSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).locallyPathConnectedSpace
  obtain ⟨F, ⟨_, hF⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    f (v 0) (representative q hs (f (v 0))) (representative_proj q hs _)
  let face (j : Fin 3) : C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3)) :=
    ⟨stdSimplex.map j.succAbove, stdSimplex.continuous_map j.succAbove⟩
  have hedge (j : Fin 3) :
      singularValue q hq hs ((TopCat.toSSet.obj (TopCat.of X)).δ j s) =
        sheet q hs (F (v (j.succAbove 1))) - sheet q hs (F (v (j.succAbove 0))) := by
    have he : (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j s) = f.comp (face j) := by
      ext z
      rw [TopCat.toSSetObjEquiv_δ_apply]
      rfl
    unfold singularValue
    rw [he]
    have hlift (t : unitInterval) :
        q (simplexEdgePath (F.comp (face j)) t) =
          simplexEdgePath (f.comp (face j)) t :=
      congr_fun hF (face j (stdSimplexHomeomorphUnitInterval.symm t))
    simpa only [ContinuousMap.comp_apply, face, ContinuousMap.coe_mk,
      stdSimplex.map_vertex] using
      pathValue_of_lift q τ hτ hne hf hq hs (simplexEdgePath (f.comp (face j)))
        (simplexEdgePath (F.comp (face j))) hlift
  simp only [hedge, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, show (1 : Fin 3) < 2 by decide,
    show (0 : Fin 3) < 2 by decide]

noncomputable def singularCochain (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex R).X 1 ⟶ R :=
  Sigma.desc (fun s => singularValue q hq hs s • 𝟙 R)

theorem singularCochain_simplex (R : ModuleCat.{u} (ZMod 2))
    (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex s ≫
      singularCochain q hq hs R = singularValue q hq hs s • 𝟙 R := Sigma.ι_desc _ _

include hτ hne hf in
theorem boundary_singularCochain (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex R).d 2 1 ≫
      singularCochain q hq hs R = 0 := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, singularCochain_simplex, comp_zero]
  simp_rw [← smul_assoc]
  rw [← Finset.sum_smul, singularValue_cocycle q τ hτ hne hf hq hs s, zero_smul]

noncomputable def homologyEvaluation (R : ModuleCat.{u} (ZMod 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).homology R 1 ⟶ R := by
  let C := (TopCat.toSSet.obj (TopCat.of X)).chainComplex R
  have h : C.toCycles 2 1 ≫ (C.iCycles 1 ≫ singularCochain q hq hs R) = 0 := by
    rw [← Category.assoc, HomologicalComplex.toCycles_i]
    exact boundary_singularCochain q τ hτ hne hf hq hs R
  exact (C.homologyIsCokernel 2 1 (by simp)).desc
    (CokernelCofork.ofπ (C.iCycles 1 ≫ singularCochain q hq hs R) h)

theorem homologyπ_evaluation (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex R).homologyπ 1 ≫
      homologyEvaluation q τ hτ hne hf hq hs R =
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex R).iCycles 1 ≫
      singularCochain q hq hs R := by
  unfold homologyEvaluation
  exact Cofork.IsColimit.π_desc
    (((TopCat.toSSet.obj (TopCat.of X)).chainComplex R).homologyIsCokernel
      2 1 (by simp))

include hτ hne hf hq hs in

theorem exists_homology_retract (R : ModuleCat.{u} (ZMod 2))
    (a : E) (L : Path a (τ a)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of X)).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of X)).homology R 1 ⟶ R), i ≫ r = 𝟙 R := by
  let p : Path (q a) (q a) :=
    ⟨⟨fun t => q (L t), hq.continuous.comp L.continuous⟩,
      congrArg q L.source, (congrArg q L.target).trans (proj_antipode q τ hf a)⟩
  have hp : pathValue q hq hs p = 1 := by
    rw [pathValue_of_lift q τ hτ hne hf hq hs p L (fun _ => rfl),
      sheet_antipode q τ hτ hne hf]
    ring
  let S := TopCat.toSSet.obj (TopCat.of X)
  let C := S.chainComplex R
  have hboundary : S.ιChainComplex (pathSimplex p) ≫ C.d 1 0 = 0 := by
    rw [SSet.ιChainComplex_d]
    simp [S, Fin.sum_univ_succ, pathSimplex_face_zero, pathSimplex_face_one]
  let γ : R ⟶ C.cycles 1 := C.liftCycles (S.ιChainComplex (pathSimplex p))
    0 (by simp) hboundary
  refine ⟨γ ≫ C.homologyπ 1, homologyEvaluation q τ hτ hne hf hq hs R, ?_⟩
  rw [Category.assoc, homologyπ_evaluation, ← Category.assoc]
  change (C.liftCycles _ _ _ _ ≫ C.iCycles 1) ≫ _ = _
  rw [HomologicalComplex.liftCycles_i, singularCochain_simplex,
    singularValue_pathSimplex q τ hτ hne hf hq hs, hp, one_smul]

end PoincareConjecture.M76.AntipodalCover
