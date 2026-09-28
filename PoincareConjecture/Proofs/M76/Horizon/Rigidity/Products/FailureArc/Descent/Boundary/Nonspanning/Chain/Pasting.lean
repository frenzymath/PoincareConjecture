import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

private theorem finite_iUnion_charts
    {F X ι J : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [Finite J]
    (e : ι → OpenPartialHomeomorph X F)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K : J → SimplicialComplex ℝ P2) (hK : ∀ i, (K i).faces.Finite)
    {g : P2 → X} (hg : ∀ i, PolyhedralPLInCharts e g (K i).space) :
    PolyhedralPLInCharts e g (⋃ i, (K i).space) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have hfinite (t : Finset J) : ∃ L : SimplicialComplex ℝ P2,
      L.faces.Finite ∧ L.space = ⋃ i ∈ t, (K i).space ∧ PolyhedralPLInCharts e g L.space := by
    induction t using Finset.induction_on with
    | empty =>
      obtain ⟨L, hL, hLs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion (E := P2)
        (fun i : Empty => nomatch i) (fun i => nomatch i)
      have hLe : L.space = ∅ := by simpa using hLs
      refine ⟨L, hL, by simp [hLe], ?_⟩
      rw [hLe]
      exact ⟨continuousOn_empty g, fun x => False.elim x.property⟩
    | @insert i t hi ih =>
      obtain ⟨L, hL, hLs, hgL⟩ := ih
      obtain ⟨N, hN, hNs⟩ := (K i).exists_finite_triangulation_union L (hK i) hL
      refine ⟨N, hN, ?_, ?_⟩
      · simp only [hNs, hLs, Finset.mem_insert, iUnion_iUnion_eq_or_left]
      · rw [hNs]
        exact PolyhedralPLInCharts.union_of_finite he (K i) L (hK i) hL (hg i) hgL
  obtain ⟨L, _, hLs, hgL⟩ := hfinite Finset.univ
  simpa only [hLs, Finset.mem_univ, iUnion_true] using hgL

theorem exists_finite_copy_pasting
    {F X ι J : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [Finite J]
    (e : ι → OpenPartialHomeomorph X F)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K : J → SimplicialComplex ℝ P2)
    (c : J → P2 → P2) (hc : ∀ i, FinitePiecewiseAffineOn (c i) (K i).space)
    (hci : ∀ i, InjOn (c i) (K i).space)
    (f : J → P2 → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) (K i).space)
    (hagree : ∀ i j x, x ∈ (K i).space → ∀ y, y ∈ (K j).space →
      c i x = c j y → f i x = f j y) (x0 : X) :
    ∃ g : P2 → X,
      PolyhedralPLInCharts e g (⋃ i, c i '' (K i).space) ∧
      (∀ i x, x ∈ (K i).space → g (c i x) = f i x) ∧
      g '' (⋃ i, c i '' (K i).space) = ⋃ i, f i '' (K i).space ∧
      ∀ U : Set X, (⋃ i, c i '' (K i).space) ∩ g ⁻¹' U =
        ⋃ i, c i '' ((K i).space ∩ (f i) ⁻¹' U) := by
  classical
  let g : P2 → X := fun z =>
    if h : ∃ p : Σ i, (K i).space, c p.1 p.2 = z then
      f (Classical.choose h).1 (Classical.choose h).2 else x0
  have hkeep (i : J) (x : P2) (hx : x ∈ (K i).space) : g (c i x) = f i x := by
    have hex : ∃ p : Σ j, (K j).space, c p.1 p.2 = c i x := ⟨⟨i, x, hx⟩, rfl⟩
    dsimp only [g]
    rw [dif_pos hex]
    exact hagree _ i _ (Classical.choose hex).2.property x hx (Classical.choose_spec hex)
  have hlocal (i : J) : ∃ L : SimplicialComplex ℝ P2,
      L.faces.Finite ∧ L.space = c i '' (K i).space ∧ PolyhedralPLInCharts e g L.space := by
    obtain ⟨q, hq, hqv⟩ := (hc i).exists_homeomorph_image (hci i)
    obtain ⟨r, hr, hrv⟩ := hq.symm
    have hrn (x : (K i).space) : r (c i x) = x := by
      rw [← hqv]
      have h := hrv (q x)
      rw [q.symm_apply_apply] at h
      exact h.symm
    have hcopy := hr
    obtain ⟨L, hL, hLs, _⟩ := hcopy
    refine ⟨L, hL, hLs, ?_⟩
    have hm : MapsTo r L.space (K i).space := by
      intro z hz
      rw [← hrv ⟨z, hLs.subset hz⟩]
      exact (q.symm ⟨z, hLs.subset hz⟩).property
    have hrL : FinitePiecewiseAffineOn r L.space := hLs.symm ▸ hr
    apply ((hf i).comp_finitePiecewiseAffineOn L hL hrL hm).congr
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hLs.subset hz
    change f i (r (c i x)) = g (c i x)
    rw [hrn ⟨x, hx⟩, hkeep i x hx]
  choose L hL hLs hgL using hlocal
  refine ⟨g, ?_, hkeep, ?_, ?_⟩
  · simpa only [hLs] using finite_iUnion_charts e he L hL hgL
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, y, hy, (hkeep i y hy).symm⟩
    · intro hz
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
      exact ⟨c i x, mem_iUnion.mpr ⟨i, x, hx, rfl⟩, hkeep i x hx⟩
  · intro U
    ext z
    constructor
    · rintro ⟨hz, hU⟩
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i, x, ⟨hx, by simpa only [mem_preimage, hkeep i x hx] using hU⟩,
        rfl⟩
    · intro hz
      obtain ⟨i, x, ⟨hx, hU⟩, rfl⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i, x, hx, rfl⟩, by
        simpa only [mem_preimage, hkeep i x hx] using hU⟩

end PoincareConjecture.M76.Dehn
