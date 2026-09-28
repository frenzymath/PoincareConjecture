import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsBall

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.exists_ball_of_regular_core
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (hP : PlanarSchoenfliesService)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n)
    (hregular : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ C : BallNeighborhoodChart E3 E3,
      C.boundary = range (fun q : UnitTwoSphere => psi i (q, 0)) ∧
      C.boundary = psi i '' ((univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ)) := by
  obtain ⟨a, b, _p, _q, z0, ha, hb, hab, hsa, hsb, howner, _hpositive,
    _hnegative, _hcard, _hp, _hq, _hpa, _hqb, _hmin, _hmax,
    hlower, hupper, _hha, _hhb, hheight⟩ := S.exists_regular_core_two_ends hzero i hregular
  let Cm : SurgeryCapTag (psi i) u :=
    Eq.mp (congrArg (fun k : Fin n => SurgeryCapTag (psi k) u) ha) (S.cap a)
  let Cp : SurgeryCapTag (psi i) u :=
    Eq.mp (congrArg (fun k : Fin n => SurgeryCapTag (psi k) u) hb) (S.cap b)
  have htransport (j k : Fin n) (h : j = k) (C : SurgeryCapTag (psi j) u) :
      let C' := Eq.mp (congrArg (fun l : Fin n => SurgeryCapTag (psi l) u) h) C
      C'.sign = C.sign ∧ C'.cutHeight = C.cutHeight ∧ C'.removal = C.removal ∧
        C'.cap = C.cap ∧ C'.seam = C.seam := by
    subst k
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hCm : Cm.sign = (S.cap a).sign ∧ Cm.cutHeight = (S.cap a).cutHeight ∧
      Cm.removal = (S.cap a).removal ∧ Cm.cap = (S.cap a).cap ∧
      Cm.seam = (S.cap a).seam := htransport _ _ ha (S.cap a)
  have hCp : Cp.sign = (S.cap b).sign ∧ Cp.cutHeight = (S.cap b).cutHeight ∧
      Cp.removal = (S.cap b).removal ∧ Cp.cap = (S.cap b).cap ∧
      Cp.seam = (S.cap b).seam := htransport _ _ hb (S.cap b)
  obtain ⟨hms, hmc, hmr, hmcap, hmseam⟩ := hCm
  obtain ⟨hps, hpc, hpr, hpcap, hpseam⟩ := hCp
  have howned : (⋃ c : {c : Fin S.capCount // S.owner c = i}, (S.cap c.1).cap) =
      (S.cap a).cap ∪ (S.cap b).cap := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := mem_iUnion.mp hy
      rcases (howner c.1).mp c.2 with hca | hcb
      · exact Or.inl (hca ▸ hc)
      · exact Or.inr (hcb ▸ hc)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨⟨a, ha⟩, hy⟩
      · exact mem_iUnion.mpr ⟨⟨b, hb⟩, hy⟩
  obtain ⟨_hKc, _hKn, _hKdef, hcover, hinter⟩ := S.retainedCore_geometry i
  have hcover' : range (fun q : UnitTwoSphere => psi i (q, 0)) =
      S.retainedCore i ∪ Cm.cap ∪ Cp.cap := by
    rw [hmcap, hpcap, union_assoc, ← howned]
    exact hcover
  have hm : S.retainedCore i ∩ Cm.cap = Cm.seam := by
    rw [hmcap, hmseam]
    exact hinter a ha
  have hp : S.retainedCore i ∩ Cp.cap = Cp.seam := by
    rw [hpcap, hpseam]
    exact hinter b hb
  have hdisjoint : Disjoint Cm.cap Cp.cap := by
    rw [hmcap, hpcap]
    exact S.caps_disjoint hab
  have horder : Cm.cutHeight + Cm.sign * Cm.removal <
      Cp.cutHeight + Cp.sign * Cp.removal := by
    rw [hmc, hms, hmr, hpc, hps, hpr]
    exact hlower.trans hupper
  have hbound : ∀ y ∈ S.retainedCore i, ⟪(u : E3), y⟫_ℝ ∈
      Icc (Cm.cutHeight + Cm.sign * Cm.removal)
        (Cp.cutHeight + Cp.sign * Cp.removal) := by
    rintro y ⟨q, hq, rfl⟩
    rw [hmc, hms, hmr, hpc, hps, hpr]
    exact hheight q hq
  have hreg : ∀ q : UnitTwoSphere, psi i (q, 0) ∈ S.retainedCore i →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0 := by
    rintro q ⟨p, hp, heq⟩
    have hpq : p = q :=
      congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) heq)
    exact hregular q (hpq ▸ hp)
  exact exists_ball_of_classified_two_caps hP (psi i) (S.embedding i) u Cm Cp
    (hms.trans hsa) (hps.trans hsb) (S.retainedCore i) hcover' hm hp hdisjoint
    horder hbound hreg

end PoincareConjecture.M25.Topology3D
