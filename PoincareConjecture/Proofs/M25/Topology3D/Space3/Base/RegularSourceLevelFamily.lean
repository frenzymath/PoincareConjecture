import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelCircle
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSurfacePullback










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_regular_source_level_family
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : E3) (t : ℝ)
    (hreg : ∀ p : UnitTwoSphere, ⟪u, psi (p, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪u, psi (x, 0)⟫_ℝ) p ≠ 0) :
    ∃ n : ℕ, ∃ q : Fin n → UnitCircle → UnitTwoSphere,
      ∃ e : Fin n ≃ ConnectedComponents (collarHeightLevel psi u t),
        (∀ i : Fin n,
          ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
          ∀ theta : UnitCircle,
            Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
        (∀ i k : Fin n, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
        (⋃ i : Fin n, range (q i)) =
          {p : UnitTwoSphere | ⟪u, psi (p, 0)⟫_ℝ = t} ∧
        ∀ i : Fin n, ∃ x : collarHeightLevel psi u t,
          ConnectedComponents.mk x = e i ∧
          (fun p : UnitTwoSphere => psi (p, 0)) '' range (q i) =
            ((↑) : collarHeightLevel psi u t → E3) '' connectedComponent x := by
  classical
  let L := collarHeightLevel psi u t
  let I := ConnectedComponents L
  let : Finite I := finite_collarHeightLevel_components psi hpsi u t hreg
  let : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  have hreps (i : Fin n) : ∃ x : L, ConnectedComponents.mk x = e i :=
    (ConnectedComponents.surjective_coe :
      Function.Surjective (ConnectedComponents.mk : L → I)) (e i)
  choose r hr using hreps
  choose g hg hgd using fun i : Fin n =>
    exists_regular_collar_component_circle psi hpsi u t hreg (r i)
  let c : Fin n → UnitCircle → E3 := fun i theta => ((g i theta).1 : E3)
  have hcinj (i : Fin n) : Function.Injective (c i) := by
    intro a b hab
    apply (g i).injective
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hcentral (i : Fin n) :
      MapsTo (c i) univ (range (fun p : UnitTwoSphere => psi (p, 0))) := by
    intro theta _htheta
    have hmem : c i theta ∈ collarHeightLevel psi u t := (g i theta).1.2
    obtain ⟨p, _hp, heq⟩ := hmem
    exact ⟨p, heq⟩
  have hlifts (i : Fin n) : ∃ q : UnitCircle → UnitTwoSphere,
      ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Function.Injective q ∧
      (∀ theta : UnitCircle, Function.Injective (mfderiv (𝓡 1) (𝓡 2) q theta)) ∧
      ∀ theta : UnitCircle, psi (q theta, 0) = c i theta := by
    obtain ⟨q, hq, hqi, hqd, hrec⟩ :=
      exists_collar_surface_source_pullback (𝓡 1) psi hpsi (c i) isOpen_univ
        (hg i).contMDiffOn (hcinj i).injOn (fun theta _ => hgd i theta) (hcentral i)
    exact ⟨q, contMDiffOn_univ.mp hq,
      fun a b hab => hqi (mem_univ a) (mem_univ b) hab,
      fun theta => hqd theta (mem_univ theta),
      fun theta => hrec theta (mem_univ theta)⟩
  choose q hq hqi hqd hrec using hlifts
  have hinj : Function.Injective (fun p : UnitTwoSphere => psi (p, 0)) := by
    intro p p' hpp'
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpp')
  have himage (i : Fin n) :
      (fun p : UnitTwoSphere => psi (p, 0)) '' range (q i) =
        ((↑) : L → E3) '' connectedComponent (r i) := by
    ext y
    constructor
    · rintro ⟨p, ⟨theta, rfl⟩, rfl⟩
      exact ⟨(g i theta).1, (g i theta).2, (hrec i theta).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨theta, htheta⟩ := (g i).surjective ⟨z, hz⟩
      refine ⟨q i theta, mem_range_self theta, ?_⟩
      exact (hrec i theta).trans
        (congrArg (fun w : connectedComponent (r i) => (w.1 : E3)) htheta)
  have hdisjoint (i k : Fin n) (hik : i ≠ k) :
      Disjoint (range (q i)) (range (q k)) := by
    have hcomp : Disjoint (connectedComponent (r i)) (connectedComponent (r k)) := by
      apply connectedComponent_disjoint
      intro heq
      apply hik
      apply e.injective
      exact (hr i).symm.trans ((ConnectedComponents.coe_eq_coe.mpr heq).trans (hr k))
    have him := Set.disjoint_image_of_injective
      (Subtype.val_injective : Function.Injective ((↑) : L → E3)) hcomp
    rw [← himage i, ← himage k] at him
    exact him.of_image
  refine ⟨n, q, e, (fun i => ⟨hq i, hqi i, hqd i⟩), hdisjoint, ?_,
    fun i => ⟨r i, hr i, himage i⟩⟩
  ext p
  constructor
  · intro hp
    obtain ⟨i, theta, rfl⟩ := mem_iUnion.mp hp
    have hmem : psi (q i theta, 0) ∈ L := by
      rw [hrec i theta]
      exact (g i theta).1.2
    obtain ⟨p', hp', heq⟩ := hmem
    exact (hinj heq) ▸ hp'
  · intro hp
    let z : L := ⟨psi (p, 0), p, hp, rfl⟩
    obtain ⟨i, hi⟩ := e.surjective (ConnectedComponents.mk z)
    have hz : z ∈ connectedComponent (r i) :=
      ConnectedComponents.coe_eq_coe'.mp (hi.symm.trans (hr i).symm)
    have hpimage : psi (p, 0) ∈
        (fun a : UnitTwoSphere => psi (a, 0)) '' range (q i) := by
      rw [himage i]
      exact ⟨z, hz, rfl⟩
    obtain ⟨p', hp', heq⟩ := hpimage
    exact mem_iUnion.mpr ⟨i, (hinj heq) ▸ hp'⟩

end PoincareConjecture.M25.Topology3D
