import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlas
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


def FamilyCutState.retainedCore
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) : Set E3 :=
  (fun q : UnitTwoSphere => psi i (q, 0)) '' S.sourceCore i


theorem FamilyCutState.sourceCore_compact_connected
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) :
    IsCompact (S.sourceCore i) ∧ IsConnected (S.sourceCore i) := by
  classical
  let I := {a : Fin S.capCount // S.owner a = i}
  let C : I → SurgeryCapTag (psi i) u := fun a =>
    Eq.mp (congrArg (fun k : Fin n => SurgeryCapTag (psi k) u) a.property) (S.cap a.val)
  have htransport (j k : Fin n) (h : j = k) (T : SurgeryCapTag (psi j) u) :
      let T' := Eq.mp (congrArg (fun l : Fin n => SurgeryCapTag (psi l) u) h) T
      T'.sourceCapInterior = T.sourceCapInterior ∧ T'.cap = T.cap := by
    subst k
    exact ⟨rfl, rfl⟩
  have hinterior (a : I) : (C a).sourceCapInterior = (S.cap a.val).sourceCapInterior :=
    (htransport _ _ a.property (S.cap a.val)).1
  have hcap (a : I) : (C a).cap = (S.cap a.val).cap :=
    (htransport _ _ a.property (S.cap a.val)).2
  have hdisjoint : ∀ a ∈ (Finset.univ : Finset I),
      ∀ b ∈ (Finset.univ : Finset I), a ≠ b → Disjoint (C a).cap (C b).cap := by
    intro a _ha b _hb hab
    rw [hcap a, hcap b]
    exact S.caps_disjoint (fun h => hab (Subtype.ext h))
  obtain ⟨hc, hn, _hs⟩ :=
    tagged_source_complement_compact_connected (Finset.univ : Finset I) C hdisjoint
  have hcore : ((univ : Set UnitTwoSphere) \
      ⋃ a ∈ (Finset.univ : Finset I), (C a).sourceCapInterior) = S.sourceCore i := by
    simp only [Finset.mem_univ, iUnion_true, hinterior, FamilyCutState.sourceCore, I]
  exact ⟨hcore ▸ hc, hcore ▸ hn⟩


theorem FamilyCutState.retainedCore_geometry
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) :
    IsCompact (S.retainedCore i) ∧ IsConnected (S.retainedCore i) ∧
      S.retainedCore i =
        (range (fun q : UnitTwoSphere => psi i (q, 0)) \
          (⋃ a : Fin S.capCount, (S.cap a).cap \ (S.cap a).seam)) ∧
      range (fun q : UnitTwoSphere => psi i (q, 0)) =
        S.retainedCore i ∪
          (⋃ a : {a : Fin S.capCount // S.owner a = i}, (S.cap a.1).cap) ∧
      ∀ a : Fin S.capCount, S.owner a = i →
        S.retainedCore i ∩ (S.cap a).cap = (S.cap a).seam := by
  classical
  have hcontinuous := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  obtain ⟨hc, hn⟩ := S.sourceCore_compact_connected i
  have hinj (j : Fin n) : Function.Injective (fun q : UnitTwoSphere => psi j (q, 0)) := by
    intro q q' hq
    exact congrArg Prod.fst ((S.embedding j).2.1 (by simp) (by simp) hq)
  refine ⟨hc.image_of_continuousOn hcontinuous.continuousOn,
    hn.image _ hcontinuous.continuousOn, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, rfl⟩, ?_⟩
      rintro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      exact (S.sourceCore_mem_and_seams.1 i q).mp hq a ha
    · rintro ⟨⟨q, rfl⟩, hq⟩
      refine ⟨q, (S.sourceCore_mem_and_seams.1 i q).mpr ?_, rfl⟩
      intro a ha
      exact hq (mem_iUnion.mpr ⟨a, ha⟩)
  · ext y
    constructor
    · rintro ⟨q, rfl⟩
      by_cases hq : q ∈ S.sourceCore i
      · exact Or.inl ⟨q, hq, rfl⟩
      · have hU : q ∈ ⋃ a : {a : Fin S.capCount // S.owner a = i},
            (S.cap a.1).sourceCapInterior := by
          by_contra hnot
          exact hq ⟨mem_univ _, hnot⟩
        obtain ⟨a, ha⟩ := mem_iUnion.mp hU
        apply Or.inr
        apply mem_iUnion.mpr
        refine ⟨a, ?_⟩
        have hmem : psi (S.owner a.1) (q, 0) ∈ (S.cap a.1).cap :=
          ⟨q, (S.cap a.1).sourceCapInterior_subset ha, rfl⟩
        simpa only [a.2] using hmem
    · rintro (⟨q, _hq, rfl⟩ | hy)
      · exact ⟨q, rfl⟩
      · obtain ⟨a, q, _hq, heq⟩ := mem_iUnion.mp hy
        exact ⟨q, by simpa only [a.2] using heq⟩
  · intro a ha
    have himage := congrArg
      (fun t : Set UnitTwoSphere => (fun q => psi (S.owner a) (q, 0)) '' t)
      (S.sourceCore_mem_and_seams.2 a)
    rw [image_inter (hinj (S.owner a))] at himage
    change (S.cap a).cap ∩ S.retainedCore (S.owner a) = (S.cap a).seam at himage
    simpa only [ha, inter_comm] using himage


theorem FamilyCutState.core_of_no_owned_caps
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n)
    (howner : ∀ a : Fin S.capCount, S.owner a ≠ i) :
    S.sourceCore i = (univ : Set UnitTwoSphere) ∧
      S.retainedCore i = range (fun q : UnitTwoSphere => psi i (q, 0)) := by
  have hcore : S.sourceCore i = (univ : Set UnitTwoSphere) := by
    apply subset_antisymm (subset_univ _)
    intro q _hq
    refine ⟨mem_univ _, ?_⟩
    intro hq
    obtain ⟨a, _ha⟩ := mem_iUnion.mp hq
    exact howner a.1 a.2
  refine ⟨hcore, ?_⟩
  rw [FamilyCutState.retainedCore, hcore, image_univ]

end PoincareConjecture.M25.Topology3D
