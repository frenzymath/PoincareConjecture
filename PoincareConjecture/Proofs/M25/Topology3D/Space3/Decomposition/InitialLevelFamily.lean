import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularInnermostDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_regular_collar_level_family
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), psi (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ m : ℕ, ∃ B : Fin m → BallNeighborhoodChart E2 E2,
      ∃ e : Fin m ≃ ConnectedComponents (collarHeightLevel psi (u : E3) t),
        Pairwise (fun i j : Fin m => Disjoint (B i).boundary (B j).boundary) ∧
        (∀ p : E2, (heightPlaneCoordinates u).symm (p, t) ∈
          psi '' (univ ×ˢ ({0} : Set ℝ)) ↔
            p ∈ (⋃ i : Fin m, (B i).boundary)) ∧
        ∀ i : Fin m, ∃ x : collarHeightLevel psi (u : E3) t,
          ConnectedComponents.mk x = e i ∧
          (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) ''
            (B i).boundary =
              ((↑) : collarHeightLevel psi (u : E3) t → E3) '' connectedComponent x := by
  classical
  let L := collarHeightLevel psi (u : E3) t
  let I := ConnectedComponents L
  let : Finite I := finite_collarHeightLevel_components psi hpsi (u : E3) t hreg
  let : Fintype I := Fintype.ofFinite I
  let m := Fintype.card I
  let e : Fin m ≃ I := (Fintype.equivFin I).symm
  have hreps (i : Fin m) : ∃ x : L, ConnectedComponents.mk x = e i :=
    (ConnectedComponents.surjective_coe :
      Function.Surjective (ConnectedComponents.mk : L → I)) (e i)
  choose r hr using hreps
  choose B hB using fun i : Fin m =>
    exists_regular_collar_component_disc hP psi hpsi u t hreg (r i)
  let lift := fun p : E2 => (heightPlaneCoordinates u).symm (p, t)
  have hlift : Function.Injective lift := by
    intro p q hpq
    exact congrArg Prod.fst ((heightPlaneCoordinates u).symm.injective hpq)
  have hheight (p : E2) : ⟪(u : E3), lift p⟫_ℝ = t := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p, t))
  have hzero : psi '' (univ ×ˢ ({0} : Set ℝ)) =
      range (fun q : UnitTwoSphere => psi (q, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hdis : Pairwise (fun i j : Fin m => Disjoint (B i).boundary (B j).boundary) := by
    intro i j hij
    have hcomp : Disjoint (connectedComponent (r i)) (connectedComponent (r j)) := by
      apply connectedComponent_disjoint
      intro heq
      apply hij
      apply e.injective
      exact (hr i).symm.trans ((ConnectedComponents.coe_eq_coe.mpr heq).trans (hr j))
    have himage := Set.disjoint_image_of_injective
      (Subtype.val_injective : Function.Injective ((↑) : L → E3)) hcomp
    rw [← hB i, ← hB j] at himage
    exact himage.of_image
  refine ⟨m, B, e, hdis, ?_, fun i => ⟨r i, hr i, hB i⟩⟩
  intro p
  rw [hzero]
  constructor
  · intro hp
    have hpL : lift p ∈ L := by
      rw [show L = collarHeightLevel psi (u : E3) t from rfl,
        collarHeightLevel_eq_central_height]
      exact ⟨hp, hheight p⟩
    let z : L := ⟨lift p, hpL⟩
    obtain ⟨i, hi⟩ := e.surjective (ConnectedComponents.mk z)
    have hz : z ∈ connectedComponent (r i) :=
      ConnectedComponents.coe_eq_coe'.mp (hi.symm.trans (hr i).symm)
    have hpB : lift p ∈ lift '' (B i).boundary := by
      rw [hB i]
      exact ⟨z, hz, rfl⟩
    exact mem_iUnion.mpr ⟨i, hlift.mem_set_image.mp hpB⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have himage : lift p ∈ lift '' (B i).boundary := ⟨p, hi, rfl⟩
    rw [hB i] at himage
    obtain ⟨z, _hz, heq⟩ := himage
    have hzL := z.2
    simp only [collarHeightLevel_eq_central_height] at hzL
    simpa only [heq] using hzL.1


theorem exists_regular_collar_band_family
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), psi (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ m : ℕ, ∃ B : Fin m → BallNeighborhoodChart E2 E2,
      ∃ e : Fin m ≃ ConnectedComponents (collarHeightLevel psi (u : E3) t),
        Pairwise (fun i j : Fin m => Disjoint (B i).boundary (B j).boundary) ∧
        (∀ i : Fin m, ∃ x : collarHeightLevel psi (u : E3) t,
          ConnectedComponents.mk x = e i ∧
          (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) ''
            (B i).boundary =
              ((↑) : collarHeightLevel psi (u : E3) t → E3) '' connectedComponent x) ∧
        ∃ d : ℝ, 0 < d ∧
          ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
            ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2) ∧
            ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2) ∧
            (∀ p : E2, Phi t p = p) ∧
            (∀ z : ℝ, HasCompactSupport (fun p : E2 => Phi z p - p)) ∧
            ∀ z ∈ Ioo (t - d) (t + d), ∀ p : E2,
              (heightPlaneCoordinates u).symm (Phi z p, z) ∈
                psi '' (univ ×ˢ ({0} : Set ℝ)) ↔
                  p ∈ (⋃ i : Fin m, (B i).boundary) := by
  obtain ⟨m, B, e, hdis, hlevel, hcomponents⟩ :=
    exists_regular_collar_level_family hP psi hpsi u t hreg
  have hregI : ∀ q : UnitTwoSphere, ⟪(u : E3), psi (q, 0)⟫_ℝ ∈ Icc t t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0 := by
    intro q hq
    exact hreg q (le_antisymm hq.2 hq.1)
  obtain ⟨d, hd, _hband, Phi, hPhi, hinverse, hidentity, hsupport, htransport⟩ :=
    exists_regular_collar_horizontal_transport psi hpsi u t t le_rfl hregI
  have hmid : (t + t) / 2 = t := by ring
  rw [hmid] at hidentity htransport
  have hzero : psi '' (univ ×ˢ ({0} : Set ℝ)) =
      range (fun q : UnitTwoSphere => psi (q, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  simp only [← hzero] at htransport
  refine ⟨m, B, e, hdis, hcomponents, d, hd, Phi, hPhi, hinverse,
    hidentity, hsupport, ?_⟩
  intro z hz p
  exact (htransport z hz p).trans (hlevel p)

end PoincareConjecture.M25.Topology3D
