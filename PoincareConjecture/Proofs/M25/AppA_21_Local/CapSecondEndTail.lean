import PoincareConjecture.Proofs.M25.AppA_21_Local.CapTubeEnds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture













theorem CapCertificate.exists_second_end_tail_of_compact_extension
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) (K : CappedTubeCertificate g)
    (hfirst : K.cap.carrier ∩ K.tube.carrier = K.cap.end_neck.carrier)
    (hdisjoint : Disjoint K.cap.closed_core C.carrier)
    (hcompact : IsCompact (K.carrier ∪ C.carrier)) :
    C.carrier ∩ K.carrier = C.carrier ∩ K.tube.carrier ∧
      C.carrier \ K.tube.carrier =
        (K.carrier ∪ C.carrier) \ K.carrier ∧
      IsCompact (C.carrier \ K.tube.carrier) ∧
      ∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        ∃ s ∈ Ioo (max d 0) C.epsilon⁻¹,
          C.carrier \ K.tube.carrier ⊆
            interior (C.carrier \ C.end_neck.region s C.epsilon⁻¹) ∧
          C.end_neck.region s C.epsilon⁻¹ ⊆ K.tube.carrier := by
  classical
  have hcore : K.carrier \ K.tube.carrier = K.cap.closed_core := by
    rw [K.cap.closed_core_eq_complement_end]
    ext x
    constructor
    · intro hx
      have hxcap : x ∈ K.cap.carrier := by
        rcases K.carrier_eq_union ▸ hx.1 with hxcap | hxtube
        · exact hxcap
        · exact False.elim (hx.2 hxtube)
      refine ⟨hxcap, ?_⟩
      intro hxend
      have hxinter : x ∈ K.cap.carrier ∩ K.tube.carrier := hfirst.symm ▸ hxend
      exact hx.2 hxinter.2
    · intro hx
      refine ⟨K.cap_subset hx.1, ?_⟩
      intro hxtube
      exact hx.2 (hfirst ▸
        (show x ∈ K.cap.carrier ∩ K.tube.carrier from ⟨hx.1, hxtube⟩))
  have hmove {x : M} (hxC : x ∈ C.carrier) (hxK : x ∈ K.carrier) :
      x ∈ K.tube.carrier := by
    by_contra hxout
    have hxcore : x ∈ K.cap.closed_core :=
      hcore ▸ (show x ∈ K.carrier \ K.tube.carrier from ⟨hxK, hxout⟩)
    exact disjoint_left.mp hdisjoint hxcore hxC
  have hinter : C.carrier ∩ K.carrier = C.carrier ∩ K.tube.carrier := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hmove hx.1 hx.2⟩,
      fun hx => ⟨hx.1, K.tube_subset hx.2⟩⟩
  have hdiff : C.carrier \ K.tube.carrier =
      (K.carrier ∪ C.carrier) \ K.carrier := by
    ext x
    constructor
    · intro hx
      exact ⟨Or.inr hx.1, fun hxK => hx.2 (hmove hx.1 hxK)⟩
    · rintro ⟨hx, hxout⟩
      rcases hx with hxK | hxC
      · exact False.elim (hxout hxK)
      · exact ⟨hxC, fun hxtube => hxout (K.tube_subset hxtube)⟩
  have hKopen : IsOpen K.carrier := by
    rw [K.carrier_eq_union]
    exact K.cap.carrier_open.union K.tube.carrier_open
  have hcompactDiff : IsCompact (C.carrier \ K.tube.carrier) := by
    rw [hdiff]
    exact hcompact.diff hKopen
  refine ⟨hinter, hdiff, hcompactDiff, ?_⟩
  intro d hd
  have hL : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hmax : max d 0 ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ :=
    ⟨(neg_lt_zero.mpr hL).trans_le (le_max_right d 0), max_lt hd.2 hL⟩
  obtain ⟨s, hs, hbuffer⟩ := C.exists_later_lower_cut_containing_compact
    hcompactDiff sdiff_subset hmax
  refine ⟨s, hs, hbuffer, ?_⟩
  intro x hx
  by_contra hxout
  exact (interior_subset (hbuffer ⟨C.end_neck_subset hx.1, hxout⟩)).2 hx

end PoincareConjecture
