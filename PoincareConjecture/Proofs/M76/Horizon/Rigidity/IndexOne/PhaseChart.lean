import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.RelativePhaseChart










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem exists_source_circle_height_chart
    {X α : Type*} [TopologicalSpace X] {R : Set X}
    (e : α → OpenPartialHomeomorph X V3)
    (p : ℝ) [Fact (0 < p)] (q : C(R, AddCircle p))
    (G : OpenPartialHomeomorph X V3)
    (hG : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (w : V3 → ℝ) (hw : K.AffineOnFaces w)
    (hlift : ∀ (y : R), (y : X) ∈ G.source → G y ∈ K.space →
      q y = (w (G y) : AddCircle p))
    (x : R) (hxG : (x : X) ∈ G.source) (hxK : G x ∈ interior K.space)
    (hreg : ∀ z ∈ K.vertices, w z ≠ w (G x)) :
    ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
      (T : OpenPartialHomeomorph X V3),
      (a : AddCircle p) = q x ∧ ell.contLinear v = 1 ∧
      (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ (y : R), (y : X) ∈ T.source →
        q y = ((ell (T y) + a : ℝ) : AddCircle p)) ∧
      ∀ (y : R), (y : X) ∈ T.source → (q y = q x ↔ ell (T y) = 0) := by
  obtain ⟨ell, v, Q, hellv, hxQ, _, hQs, _, hQPL, hheight⟩ :=
    K.exists_nonvertex_height_chart hK hw hxK hreg
  let a := w (G x)
  let W := ell ⁻¹' Ioo (a - p / 2) (a + p / 2)
  have hW : IsOpen W := isOpen_Ioo.preimage ell.continuous
  let I := OpenPartialHomeomorph.ofSet W hW
  let T := (G.trans Q).trans I
  let ell0 := ell - ContinuousAffineMap.const ℝ V3 a
  have hp : 0 < p := Fact.out
  have hax : (a : AddCircle p) = q x := (hlift x hxG (interior_subset hxK)).symm
  have hxT : (x : X) ∈ T.source := by
    refine ⟨⟨hxG, hxQ⟩, ?_⟩
    change ell (Q (G x)) ∈ Ioo (a - p / 2) (a + p / 2)
    rw [hheight _ hxQ]
    change a - p / 2 < a ∧ a < a + p / 2
    constructor <;> linarith
  have hI : I ∈ piecewiseAffineGroupoid V3 :=
    ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) hW,
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) hW⟩
  have hphase (y : R) (hy : (y : X) ∈ T.source) :
      q y = (ell (T y) : AddCircle p) := by
    change q y = (ell (Q (G y)) : AddCircle p)
    rw [hheight (G y) hy.1.2]
    exact hlift y hy.1.1 (interior_subset (hQs hy.1.2))
  refine ⟨a, ell0, v, T, hax, ?_, hxT, ?_, ?_, ?_, ?_⟩
  · simpa only [ell0, ContinuousAffineMap.sub_contLinear,
      ContinuousAffineMap.const_contLinear, sub_zero] using hellv
  · change ell (Q (G x)) - a = 0
    rw [hheight _ hxQ]; exact sub_self a
  · intro i
    simpa only [T, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans
        ((piecewiseAffineGroupoid V3).trans (hG i) hQPL) hI
  · intro y hy
    change q y = ((ell (T y) - a + a : ℝ) : AddCircle p)
    simpa only [sub_add_cancel] using hphase y hy
  · intro y hy
    have hyW : ell (T y) ∈ Ioo (a - p / 2) (a + p / 2) := hy.2
    have hyI : ell (T y) ∈ Ico (a - p / 2) (a - p / 2 + p) :=
      ⟨hyW.1.le, by linarith [hyW.2]⟩
    have haI : a ∈ Ico (a - p / 2) (a - p / 2 + p) := by
      constructor <;> linarith
    rw [hphase y hy, ← hax, AddCircle.coe_eq_coe_iff_of_mem_Ico hyI haI]
    change ell (T y) = a ↔ ell (T y) - a = 0
    exact sub_eq_zero.symm

end PoincareConjecture.M76.HamiltonIntervalTorus
