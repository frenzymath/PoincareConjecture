import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Lift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.JointPLComposition

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem circle_lift_endpoint_eq_of_relative_homotopy
    {p : ℝ} [Fact (0 < p)]
    (H : C(I × I, AddCircle p)) (r₀ r₁ : C(I, ℝ))
    (h₀ : ∀ s, H (0, s) = (r₀ s : AddCircle p))
    (h₁ : ∀ s, H (1, s) = (r₁ s : AddCircle p))
    (hleft : ∀ t, H (t, 0) = H (0, 0))
    (hright : ∀ t, H (t, 1) = H (0, 1))
    (hbase : r₀ 0 = r₁ 0) : r₀ 1 = r₁ 1 := by
  let cov := AddCircle.isCoveringMap_coe p
  let L := cov.liftHomotopy H r₀ h₀
  have hL (x : I × I) : (L x : AddCircle p) = H x :=
    congrFun (cov.liftHomotopy_lifts H r₀ h₀) x
  have hL₀ (s : I) : L (0, s) = r₀ s := cov.liftHomotopy_zero H r₀ h₀ s
  have hfix₀ (t : I) : L (t, 0) = r₀ 0 := by
    rw [cov.const_of_comp (g := fun t : I => L (t, 0)) (by fun_prop)
      (fun t u => by rw [hL, hL, hleft t, hleft u]) t 0, hL₀]
  have hfix₁ (t : I) : L (t, 1) = r₀ 1 := by
    rw [cov.const_of_comp (g := fun t : I => L (t, 1)) (by fun_prop)
      (fun t u => by rw [hL, hL, hright t, hright u]) t 0, hL₀]
  have hsame : (fun s : I => L (1, s)) = r₁ :=
    cov.eq_of_comp_eq (by fun_prop) r₁.continuous
      (funext fun s => (hL (1, s)).trans (h₁ s)) 0 ((hfix₀ 1).trans hbase)
  exact (hfix₁ 1).symm.trans (congrFun hsame 1)

theorem annular_lift_winding_invariant
    (gamma : C(I, Ann)) (H : I → Ann ≃ₜ Ann)
    (hH : Continuous (fun x : I × Ann => H x.1 x.2))
    (hzero : H 0 = Homeomorph.refl Ann)
    (hrims : ∀ t side z, H t (annulusRimPoint side z) = annulusRimPoint side z)
    (hgamma₀ : gamma 0 = annulusRimPoint false 0)
    (hgamma₁ : gamma 1 = annulusRimPoint true 0)
    (r₀ r₁ : C(I, P2))
    (hheight₀ : ∀ s, (r₀ s).2 ∈ Icc (-1 : ℝ) 1)
    (hheight₁ : ∀ s, (r₁ s).2 ∈ Icc (-1 : ℝ) 1)
    (hproject₀ : ∀ s, annulusMap 8 (by norm_num)
      (((r₀ s).1 : Circle), (r₀ s).2) = gamma s)
    (hproject₁ : ∀ s, annulusMap 8 (by norm_num)
      (((r₁ s).1 : Circle), (r₁ s).2) = H 1 (gamma s))
    (hbase : (r₀ 0).1 = (r₁ 0).1) : (r₀ 1).1 = (r₁ 1).1 := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨C, hC⟩ := exists_annulus_homeomorph
    (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : 4 * (1 : ℝ) < 8)
  let F : C(I × I, Circle) :=
    ⟨fun x => (C.symm (H x.1 (gamma x.2))).1,
      continuous_fst.comp (C.symm.continuous.comp
        (hH.comp (continuous_fst.prodMk (gamma.continuous.comp continuous_snd))))⟩
  have hcoord (r : C(I, P2)) (hheight : ∀ s, (r s).2 ∈ Icc (-1 : ℝ) 1)
      (s : I) (y : Ann)
      (hy : annulusMap 8 (by norm_num) (((r s).1 : Circle), (r s).2) = y) :
      (C.symm y).1 = ((r s).1 : Circle) := by
    have hv : C (((r s).1 : Circle), ⟨(r s).2, hheight s⟩) = y :=
      Subtype.ext ((hC _).trans hy)
    rw [← hv, C.symm_apply_apply]
  exact circle_lift_endpoint_eq_of_relative_homotopy F
    ⟨fun s => (r₀ s).1, by fun_prop⟩ ⟨fun s => (r₁ s).1, by fun_prop⟩
    (fun s => by
      change (C.symm (H 0 (gamma s))).1 = _
      rw [hzero]
      exact hcoord r₀ hheight₀ s (gamma s) (hproject₀ s))
    (fun s => hcoord r₁ hheight₁ s (H 1 (gamma s)) (hproject₁ s))
    (fun t => by change (C.symm (H t (gamma 0))).1 = (C.symm (H 0 (gamma 0))).1
                 rw [hgamma₀, hrims, hrims])
    (fun t => by change (C.symm (H t (gamma 1))).1 = (C.symm (H 0 (gamma 1))).1
                 rw [hgamma₁, hrims, hrims]) hbase

theorem exists_zero_winding_annular_lift_after_joint_PL_isotopy
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → P2) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : P2))
    (hgamma₀ : gamma 0 = annulusRimPoint false 0)
    (hgamma₁ : gamma 1 = annulusRimPoint true 0)
    (r₀ : ℝ → P2) (hr₀ : FinitePiecewiseAffineOn r₀ (Icc 0 1))
    (hr₀zero : r₀ 0 = (0, -1)) (hr₀one : r₀ 1 = (0, 1))
    (hheight₀ : ∀ t : I, (r₀ t).2 ∈ Icc (-1 : ℝ) 1)
    (hproject₀ : ∀ t : I, annulusMap 8 (by norm_num)
      (((r₀ t).1 : Circle), (r₀ t).2) = gamma t)
    (G : Ann ≃ₜ Ann) (hG : HasJointPLAnnularIsotopy G) :
    ∃ r : ℝ → P2, FinitePiecewiseAffineOn r (Icc 0 1) ∧
      InjOn r (Icc 0 1) ∧ r 0 = (0, -1) ∧ r 1 = (0, 1) ∧
      (∀ t : I, (r t).2 = depth 8 (G (gamma t) : P2)) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = G (gamma t)) ∧
      ∀ (t s : I) (k : ℤ), r t = r s + (32 * (k : ℝ), 0) → t = s ∧ k = 0 := by
  let gamma' : C(I, Ann) := ⟨fun t => G (gamma t), G.continuous.comp gamma.continuous⟩
  obtain ⟨v, hv, hGv⟩ := hG.isFinitePL
  have hvf : FinitePiecewiseAffineOn (v ∘ f) (Icc 0 1) := hv.comp hf (by
    intro t ht
    rw [hfv ⟨t, ht⟩]
    exact (gamma ⟨t, ht⟩).property)
  obtain ⟨n, r, hr, hi, hrzero, hrone, hdepth, hproj, htrans⟩ :=
    exists_finitePL_annular_arc_lift gamma' (G.injective.comp hinj) (v ∘ f) hvf
      (fun t => by change v (f t) = _; rw [hfv, ← hGv]; rfl)
      (by change G (gamma 0) = _; rw [hgamma₀, hG.rims])
      (by change G (gamma 1) = _; rw [hgamma₁, hG.rims])
  obtain ⟨H, _, _, hzero, hone, _, _, _, _, hc, _, hrims⟩ := hG
  let R₀ : C(I, P2) := ⟨fun t => r₀ t, hr₀.continuousOn.domRestrict⟩
  let R₁ : C(I, P2) := ⟨fun t => r t, hr.continuousOn.domRestrict⟩
  have hwind := annular_lift_winding_invariant gamma H hc hzero hrims hgamma₀ hgamma₁
    R₀ R₁ hheight₀
    (fun t => by change (r t).2 ∈ _; rw [hdepth]; exact mem_squareAnnulus_iff_depth.mp (gamma' t).property)
    hproject₀ (fun t => by rw [hone]; exact hproj t)
    (by change (r₀ 0).1 = (r 0).1; rw [hr₀zero, hrzero])
  have hrone' : r 1 = (0, 1) := by
    apply Prod.ext
    · change (r₀ 1).1 = (r 1).1 at hwind
      rw [hr₀one] at hwind
      exact hwind.symm
    · rw [hrone]
  exact ⟨r, hr, hi, hrzero, hrone', hdepth, hproj, htrans⟩

end PoincareConjecture.M76.Dehn
