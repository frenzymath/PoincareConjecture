import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CircleCapEulerCount
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "V2" => (Fin 2 → ℝ)

theorem circle_incidence (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (gamma : sphere (0 : V2) 1 ≃ₜ K.space) (hgamma : gamma.IsFinitePL) :
    (∀ s ∈ K.faces, s.card ≤ 2) ∧
    (∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 2 ∧ s ⊆ t) ∧
    IsConnected K.space ∧
    (∀ v ∈ K.vertices, {t : Finset E | t ∈ K.faces ∧ t.card = 2 ∧ v ∈ t}.ncard = 2) ∧
    K.surfaceEulerCount = 0 := by
  classical
  obtain ⟨hdim, n, P, hPi, hP, _, hPs, hPf, _⟩ :=
    exists_original_boundary_circle_order gamma hgamma K hK rfl
  have hconn : IsConnected K.space := by
    obtain ⟨g, hg, hgv⟩ := hgamma
    have himage : g '' sphere (0 : V2) 1 = K.space := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hgv ⟨x, hx⟩) ▸ (gamma ⟨x, hx⟩).property
      · intro hy
        let x := gamma.symm ⟨y, hy⟩
        exact ⟨x, x.property, (hgv x).symm.trans
          (congrArg Subtype.val (gamma.apply_symm_apply ⟨y, hy⟩))⟩
    rw [← himage]
    exact (isConnected_sphere (by simp) (0 : V2) zero_le_one).image g hg.continuousOn
  refine ⟨hdim, ?_, hconn, ?_, circle_surfaceEulerCount K hK gamma hgamma⟩
  · intro s hs
    obtain ⟨j, hsj⟩ := ((hPf s).mp hs).2
    have hnext : j ≠ finRotate (n + 3) j := by
      intro h
      have hh : (1 : Fin (n + 3)) = 0 := add_left_cancel
        (show j + 1 = j + 0 by simpa only [finRotate_apply, add_zero] using h.symm)
      have := congrArg Fin.val hh
      norm_num at this
    exact ⟨{P j, P (finRotate (n + 3) j)},
      (hPf _).mpr ⟨Finset.insert_nonempty _ _, j, subset_rfl⟩,
      Finset.card_pair (hPi.ne hnext), hsj⟩
  · intro v hv
    have hdegree := K.polygon_carrier_two_neighbors hK P hP hPi hPs ⟨v, hv⟩
    rw [K.ncard_edgeGraph_neighborSet, K.ncard_faceLink_vertices_eq_cofaces] at hdegree
    simpa only [Finset.card_singleton, Finset.singleton_subset_iff] using hdegree

end PoincareConjecture.M76.Dehn.Annuli
