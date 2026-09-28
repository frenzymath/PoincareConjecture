import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SquareCircle
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PeriodicSquarePL

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "C32" => AddCircle (4 * (8 : ℝ))

private theorem exists_finite_closed_interval {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ ℝ, K.faces.Finite ∧ K.space = Icc a b := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc hab
  exact ⟨K, hK, hKs⟩

theorem exists_square_rim_map_of_PL_period
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (f : C32 → X)
    (hperiod : PolyhedralPLInCharts e
      (fun t : ℝ => f ((32 * t : ℝ) : C32)) (Icc (0 : ℝ) 1)) :
    ∃ (j : C32 ≃ₜ Q2) (q : V2 → X), PolyhedralPLInCharts e q Q2 ∧
      ∀ z, q (j z) = f z := by
  classical
  let : Fact (0 < (4 * (8 : ℝ))) := ⟨by norm_num⟩
  obtain ⟨j, _, _, _, hu⟩ := Dehn.exists_square_circle_coordinates
  let u : ℝ → V2 := fun t => j ((32 * t : ℝ) : C32)
  let q : V2 → X := fun x => if hx : x ∈ Q2 then f (j.symm ⟨x, hx⟩) else f 0
  have hq (z : C32) : q (j z) = f z := by
    simp only [q, dif_pos (j z).property, j.symm_apply_apply]
  let I (b : Bool) : Set ℝ := if b then Icc (1 / 2) 1 else Icc 0 (1 / 2)
  have hI (b : Bool) : I b ⊆ Icc (0 : ℝ) 1 := by
    cases b <;> simp only [I, Bool.false_eq_true, if_false, if_true]
    · intro t ht
      exact ⟨ht.1, by linarith [ht.2]⟩
    · intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩
  have hfinite (b : Bool) :
      ∃ K : SimplicialComplex ℝ ℝ, K.faces.Finite ∧ K.space = I b := by
    cases b
    · exact exists_finite_closed_interval (by norm_num : (0 : ℝ) < 1 / 2)
    · exact exists_finite_closed_interval (by norm_num : (1 / 2 : ℝ) < 1)
  have hinj (b : Bool) : InjOn u (I b) := by
    intro s hs t ht h
    have hs01 := hI b hs
    have ht01 := hI b ht
    have hcoe : ((32 * s : ℝ) : C32) = ((32 * t : ℝ) : C32) :=
      j.injective (Subtype.ext h)
    have hs32 : 32 * s ∈ Icc (0 : ℝ) (4 * 8) :=
      ⟨by linarith [hs01.1], by linarith [hs01.2]⟩
    have ht32 : 32 * t ∈ Icc (0 : ℝ) (4 * 8) :=
      ⟨by linarith [ht01.1], by linarith [ht01.2]⟩
    rcases (AddCircle.coe_eq_coe_iff_eq_or_endpoints hs32 ht32).mp hcoe with
      hst | ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
    · linarith
    · cases b <;> simp only [I, Bool.false_eq_true, if_false, if_true] at hs ht
      · linarith [ht.2]
      · linarith [hs.1]
    · cases b <;> simp only [I, Bool.false_eq_true, if_false, if_true] at hs ht
      · linarith [hs.2]
      · linarith [ht.1]
  have hpieces (b : Bool) : ∃ K : SimplicialComplex ℝ V2,
      K.faces.Finite ∧ K.space = u '' I b ∧ PolyhedralPLInCharts e q K.space := by
    obtain ⟨J, hJ, hJs⟩ := hfinite b
    have hsub : J.space ⊆ Icc (0 : ℝ) 1 := hJs.subset.trans (hI b)
    have hcomp : PolyhedralPLInCharts e (q ∘ u) J.space :=
      (hperiod.restrict_finite J hJ hsub).congr (fun t _ => (hq _).symm)
    have hpiece := hcomp.exists_image_of_finitePL_embedding
      (hu.restrict J hJ hsub) ((hinj b).mono hJs.subset)
    simpa only [hJs] using hpiece
  obtain ⟨K, hK, hKs, hqK⟩ := hpieces false
  obtain ⟨L, hL, hLs, hqL⟩ := hpieces true
  have hintervals : I false ∪ I true = Icc (0 : ℝ) 1 := by
    apply Subset.antisymm (union_subset (hI false) (hI true))
    intro t ht
    by_cases h : t ≤ 1 / 2
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨(lt_of_not_ge h).le, ht.2⟩
  have himage : u '' Icc (0 : ℝ) 1 = Q2 := by
    apply Subset.antisymm
    · rintro x ⟨t, _, rfl⟩
      exact (j _).property
    · intro x hx
      obtain ⟨s, hs, hsz⟩ := AddCircle.eq_coe_Ico (j.symm ⟨x, hx⟩)
      refine ⟨s / 32, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      have hmul : 32 * (s / 32) = s := by ring
      dsimp only [u]
      rw [hmul, hsz, j.apply_symm_apply]
  have hwhole : K.space ∪ L.space = Q2 := by
    rw [hKs, hLs, ← image_union, hintervals, himage]
  exact ⟨j, q, hwhole ▸ hqK.union_of_finite hcompat K L hK hL hqL, hq⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
