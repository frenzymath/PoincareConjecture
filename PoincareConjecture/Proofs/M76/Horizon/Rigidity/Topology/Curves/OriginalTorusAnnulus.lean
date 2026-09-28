import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.TorusBandAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.FinitePLEssentialCircle

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem SourceSquareMap.exists_original_coordinate_annulus
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    (e : ι → OpenPartialHomeomorph X V) {S : Set X}
    (H : K.space ≃ₜ S) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X))
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ S)
      (b : C(AddCircle p × Icc (-r) r, S))
      (B : Set X) (hBS : B ⊆ S) (A : Ann ≃ₜ B) (j : P2 → X) (N : Set S),
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      IsEmbedding b ∧
      (∀ z, b z = h (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p))) ∧
      range (fun z => (b z : X)) = B ∧ IsCompact B ∧ IsClosed B ∧
      PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
      N = b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r} ∧ IsOpen N ∧
      N ⊆ (Subtype.val : S → X) ⁻¹' B ∧
      (∀ z : Ann, (⟨A z, hBS (A z).property⟩ : S) ∈ N ↔
        -1 < depth 8 (z : P2) ∧ depth 8 (z : P2) < 1) ∧
      (∀ z : Circle, (A (Dehn.annulusCoreCircle z) : X) =
        (h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X)) ∧
      ∃ retract : C(S, AddCircle p), ∀ z, retract (b z) = z.1 := by
  classical
  obtain ⟨h, b, A, hval, hb, hbval, hA, _, hopen, hperiod, hinner, retract, hretract⟩ :=
    M.exists_finitePL_coordinate_annulus hr hwidth
  have hAK : range (fun z => (b z : E)) ⊆ K.space := by
    rintro _ ⟨z, rfl⟩
    exact (b z).property
  obtain ⟨a, ha, haval⟩ := hA
  let Q : Ann → S := fun z => H ⟨A z, hAK (A z).property⟩
  have hQi : IsEmbedding Q := H.isEmbedding.comp
    ((IsEmbedding.inclusion hAK).comp A.isEmbedding)
  let q : Ann → X := fun z => (Q z : X)
  have hqi : IsEmbedding q := IsEmbedding.subtypeVal.comp hQi
  let B : Set X := range q
  have hBS : B ⊆ S := by
    rintro _ ⟨z, rfl⟩
    exact (Q z).property
  let A' : Ann ≃ₜ B := hqi.toHomeomorph
  let j : P2 → X := F ∘ a
  have hmap : MapsTo a Ann K.space := by
    intro z hz
    rw [← haval ⟨z, hz⟩]
    exact hAK (A ⟨z, hz⟩).property
  obtain ⟨J, hJ, hJs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  have hj : PolyhedralPLInCharts e j Ann := by
    rw [← hJs] at ha hmap ⊢
    exact hF.comp_finitePiecewiseAffineOn J hJ ha hmap
  have hjval (z : Ann) : j z = (A' z : X) := by
    change F (a z) = (H ⟨A z, hAK (A z).property⟩ : X)
    rw [← haval z]
    exact hFval ⟨A z, hAK (A z).property⟩
  let b' : C(AddCircle p × Icc (-r) r, S) :=
    ⟨fun z => H (b z), H.continuous.comp b.continuous⟩
  have hrange : range (fun z => (b' z : X)) = B := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      let y : range (fun w => (b w : E)) := ⟨b z, z, rfl⟩
      refine ⟨A.symm y, ?_⟩
      change (H ⟨A (A.symm y), _⟩ : X) = (H (b z) : X)
      rw [A.apply_symm_apply]
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := (A z).property
      refine ⟨w, ?_⟩
      change (H (b w) : X) = (H ⟨A z, _⟩ : X)
      exact congrArg (fun y : K.space => (H y : X)) (Subtype.ext hw)
  have hcompact : IsCompact B := by
    rw [← hrange]
    exact isCompact_range (continuous_subtype_val.comp b'.continuous)
  let N : Set S := b' '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}
  have hNopen : IsOpen N := by
    have heq : N = H '' (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) :=
      (image_image H b _).symm
    rw [heq]
    exact H.isOpenMap _ hopen
  have hNsub : N ⊆ (Subtype.val : S → X) ⁻¹' B := by
    rintro _ ⟨z, _, rfl⟩
    exact hrange.subset ⟨z, rfl⟩
  have hNmark (z : Ann) : (⟨A' z, hBS (A' z).property⟩ : S) ∈ N ↔
      -1 < depth 8 (z : P2) ∧ depth 8 (z : P2) < 1 := by
    rw [← hinner z]
    constructor
    · rintro ⟨w, hw, heq⟩
      have h := H.injective heq
      exact ⟨w, hw, congrArg Subtype.val h⟩
    · rintro ⟨w, hw, heq⟩
      exact ⟨w, hw, congrArg H (Subtype.ext heq)⟩
  have hcore (z : Circle) : (A' (Dehn.annulusCoreCircle z) : X) =
      ((h.trans H) (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
        (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X) := by
    let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
    let s := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
    have hs : (s : ℝ) ∈ Icc 0 (4 * (8 : ℝ)) :=
      ⟨s.property.1, by simpa only [zero_add] using s.property.2.le⟩
    have hsz : ((s : ℝ) : Circle) = z := AddCircle.coe_equivIco
    have hpoint : Dehn.annulusCoreCircle z =
        (⟨annulusMap 8 (by norm_num) (((s : ℝ) : Circle), (0 : ℝ)),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _
            ⟨0, by norm_num⟩⟩ : Ann) := by
      apply Subtype.ext
      rw [Dehn.annulusCoreCircle_apply, hsz]
    have hp0 := hperiod (s : ℝ) hs ⟨0, by norm_num⟩
    have hscale : (((32 : ℝ)⁻¹ * p * (s : ℝ) : ℝ) : AddCircle p) =
        AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z := by
      rw [← hsz, AddCircle.homeomorphAddCircle_apply_mk]
      congr 1
      ring
    rw [← hpoint, hscale] at hp0
    have hz : (⟨A (Dehn.annulusCoreCircle z), hAK (A _).property⟩ : K.space) =
        h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) := by
      apply Subtype.ext
      rw [hp0, hbval]
      simp
    exact congrArg (fun y : K.space => (H y : X)) hz
  exact ⟨h.trans H, b', B, hBS, A', j, N,
    fun z => congrArg H (hval z), H.isEmbedding.comp hb,
    fun z => congrArg H (hbval z), hrange, hcompact, hcompact.isClosed,
    hj, hjval, rfl, hNopen, hNsub, hNmark, hcore,
    ⟨fun x => retract (H.symm x), retract.continuous.comp H.symm.continuous⟩,
    fun z => by change retract (H.symm (H (b z))) = z.1; rw [H.symm_apply_apply]; exact hretract z⟩

end PoincareConjecture.M76.PeriodicSquare
