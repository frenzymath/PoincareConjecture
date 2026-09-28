import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslationPL









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V0" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "pi" => latticeCoordinateProjection (Fin 0) (Fin 3) L0


noncomputable def hamiltonZeroTargetVectorTranslation : C(V3 × X0, X0) :=
  ⟨fun z => (z.2.1, z.2.2 + QuotientAddGroup.mk z.1),
    (continuous_snd.fst).prodMk
      (continuous_snd.snd.add (QuotientAddGroup.continuous_mk.comp continuous_fst))⟩

@[simp] theorem hamiltonZeroTargetVectorTranslation_zero (y : X0) :
    hamiltonZeroTargetVectorTranslation (0, y) = y := by
  change (y.1, y.2 + QuotientAddGroup.mk (0 : V3)) = y
  simp

theorem hamiltonZeroTargetVectorTranslation_mk (w : V3)
    (x : Fin 0 → ℝ) (v : V3) :
    hamiltonZeroTargetVectorTranslation (w, (x, QuotientAddGroup.mk v)) =
      (x, QuotientAddGroup.mk (v + w)) := by
  change (x, QuotientAddGroup.mk v + QuotientAddGroup.mk w) = _
  rw [← QuotientAddGroup.mk_add]

theorem hamiltonZeroTargetVectorTranslation_coordinates (w : V3) (y : X0) :
    Q0 (hamiltonZeroTargetVectorTranslation (w, y)) =
      (((Q0 y).1.1 + (w 0 : C0), (Q0 y).1.2 + (w 1 : C0)),
        (Q0 y).2 + (w 2 : C0)) := by
  obtain ⟨x, v⟩ := y
  induction v using Quotient.inductionOn with
  | h v =>
    rw [hamiltonZeroTargetVectorTranslation_mk]
    change ((((v 0 + w 0 : ℝ) : C0), ((v 1 + w 1 : ℝ) : C0)),
      ((v 2 + w 2 : ℝ) : C0)) = _
    simp only [AddCircle.coe_add]
    rfl



theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetVectorTranslation
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {Y : E → X0} {w : E → V3} {S : Set E}
    (hY : PolyhedralPLInCharts d Y S) (hw : FinitePiecewiseAffineOn w S) :
    PolyhedralPLInCharts d (fun x => hamiltonZeroTargetVectorTranslation (w x, Y x)) S := by
  classical
  let n : V3 →L[ℝ] V0 := ContinuousLinearMap.pi fun j =>
    match j with
    | Sum.inl i => Fin.elim0 i
    | Sum.inr i => ContinuousLinearMap.proj i
  have htranslation (u : V3) (v : V0) :
      hamiltonZeroTargetVectorTranslation (u, pi v) = pi (v + n u) := by
    rw [show pi v = ((fun i => v (Sum.inl i)),
      QuotientAddGroup.mk (fun j => v (Sum.inr j))) from rfl,
      hamiltonZeroTargetVectorTranslation_mk]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  refine ⟨hamiltonZeroTargetVectorTranslation.continuous.comp_continuousOn
    (hw.continuousOn.prodMk hY.continuousOn), ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
    (fun _ => ℝ)).toContinuousAffineEquiv
  let a := a0.trans split.symm
  have ha (z : V3) (hz : z ∈ (d i).target) : pi (a z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v : E → V0 := a ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp a.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (a (d i (Y y))) = Y y
    rw [ha _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hn : FinitePiecewiseAffineOn (fun y => n (w y)) J.space := by
    exact (hw.restrict J hJ hJS).postcomp n.toContinuousAffineMap
  have hlocal : PolyhedralPLInCharts d
      (fun y => hamiltonZeroTargetVectorTranslation (w y, Y y)) J.space := by
    apply (hd.polyhedralPL_projection (hv.add hn)).congr
    intro y hy
    change pi (v y + n (w y)) = hamiltonZeroTargetVectorTranslation (w y, Y y)
    rw [← htranslation, hprojection y hy]
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  obtain ⟨j, N, W, hN, hNJ, hW, hxW, hWN, htarget, hformula⟩ :=
    hlocal.coordinates ⟨x, hxJ⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxJ⟩ : J.space) ∈ Subtype.val ⁻¹' O
    rw [hOW]
    exact hxW
  refine ⟨j, N, V ∩ (Subtype.val : S → E) ⁻¹' O,
    hN, hNJ.trans hJS, hV.inter (hO.preimage continuous_subtype_val),
    ⟨hxV, hxO⟩, ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzJ : (z : E) ∈ J.space := hVJ ⟨z, hz.1, rfl⟩
  have hzW : (⟨z, hzJ⟩ : J.space) ∈ W := by
    rw [← hOW]
    exact hz.2
  exact hWN ⟨⟨z, hzJ⟩, hzW, rfl⟩

end PoincareConjecture.M76
