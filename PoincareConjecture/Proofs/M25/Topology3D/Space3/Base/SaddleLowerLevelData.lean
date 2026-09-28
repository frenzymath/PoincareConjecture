import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleLowerSourceLegs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleDiscBoundaries
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set Function Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_lowerLevelData_of_two_circles
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let c : ℝ := f D.point
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ delta : ℝ, 0 < delta → delta < epsilon →
      ∀ q : Fin 2 → UnitCircle → UnitTwoSphere,
        (∀ b : Fin 2,
          ContMDiff (𝓡 1) (𝓡 2) ∞ (q b) ∧
          Function.Injective (q b) ∧
          ∀ theta : UnitCircle,
            Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q b) theta)) →
        (∀ b k : Fin 2, b ≠ k →
          Disjoint (range (q b)) (range (q k))) →
        (⋃ b : Fin 2, range (q b)) =
          {p : UnitTwoSphere | f p = c - delta} →
        ∃ W : SaddleLowerLevelData D,
          W.level = c - delta ∧
          (∀ b : Fin 2, ∀ theta : UnitCircle,
            W.leg b (theta, W.level) = q b theta) ∧
          (∀ i : Fin D.capCount,
            (D.cap i).sign = 1 ↔ ∃ b : Fin 2, W.label b = i) ∧
          Disjoint (W.disc 0).boundary (W.disc 1).boundary := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let c := f D.point
  let gap : Fin D.capCount → ℝ := fun i => D.cutRadius i - (D.cap i).removal
  have hgap (i : Fin D.capCount) : 0 < gap i :=
    sub_pos.mpr (D.removal_lt_cutRadius i)
  let S : Finset ℝ := insert 1 (Finset.univ.image gap)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hSpos (x : ℝ) (hx : x ∈ S) : 0 < x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hgap i
  have hminpos : 0 < S.min' hS := hSpos _ (Finset.min'_mem S hS)
  let epsilon := S.min' hS / 2
  have hepsilon : 0 < epsilon := half_pos hminpos
  have hepsilonGap (i : Fin D.capCount) : epsilon < gap i := by
    have hi : gap i ∈ S := Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    exact (half_lt_self hminpos).trans_le (Finset.min'_le S (gap i) hi)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro delta hdelta hdeltaSmall q hq hdisjoint hlevel
  have hsmall (i : Fin D.capCount) : delta < D.cutRadius i - (D.cap i).removal :=
    hdeltaSmall.trans (hepsilonGap i)
  obtain ⟨label, eta, leg, hlabelInjective, hlabelAll, hseams,
    hsource, hsmooth, hinverse, hheight, htop, hbottom, hlegDis, hcover⟩ :=
    exists_saddle_lower_source_legs psi hpsi u D delta hdelta hsmall
      q hq hdisjoint hlevel
  let z := c - delta
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  have hlabelLower (b : Fin 2) : (D.cap (label b)).sign = 1 :=
    (hlabelAll (label b)).mpr ⟨b, rfl⟩
  have hlegSource (b : Fin 2) :
      (univ : Set UnitCircle) ×ˢ Icc (ell (label b)) z ⊆ (leg b).source := by
    rintro ⟨theta, t⟩ ⟨_, ht⟩
    rw [(hsource b).2]
    refine ⟨mem_univ _, ?_, ?_⟩ <;> linarith [(hsource b).1, ht.1, ht.2]
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let L := heightPlaneCoordinates u
  let curve : Fin 2 → UnitCircle → E3 := fun b theta => j (q b theta)
  let projected : Fin 2 → UnitCircle → E2 := fun b theta => (L (curve b theta)).1
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro p r hpr
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpr)
  have hcurveHeight (b : Fin 2) (theta : UnitCircle) :
      ⟪(u : E3), curve b theta⟫_ℝ = z := by
    have hx : q b theta ∈ ⋃ k : Fin 2, range (q k) :=
      mem_iUnion.mpr ⟨b, mem_range_self theta⟩
    rw [hlevel] at hx
    exact hx
  have hprojected (b : Fin 2) : IsPlanarEmbedding (projected b) := by
    have hcs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ (curve b) := hj.comp (hq b).1
    have hci : Injective (curve b) := hji.comp (hq b).2.1
    have hcd (theta : UnitCircle) :
        Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (curve b) theta) := by
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (j ∘ q b) theta)
      rw [mfderiv_comp theta (hj.mdifferentiable (by simp) _)
        ((hq b).1.mdifferentiable (by simp) theta)]
      exact (collar_central_mfderiv_injective psi hpsi _).comp ((hq b).2.2 theta)
    exact isPlanarEmbedding_height_projection u (curve b) hcs hci hcd z (hcurveHeight b)
  let planar : ∀ b : Fin 2, PlanarSchoenfliesData (projected b) :=
    fun b => Classical.choice (hP.1 (projected b) (hprojected b))
  let disc : Fin 2 → BallNeighborhoodChart E2 E2 :=
    fun b => (planar b).ballNeighborhoodChart
  have hdiscBoundary (b : Fin 2) :
      (fun x : E2 => L.symm (x, z)) '' (disc b).boundary =
        range (fun theta => psi (leg b (theta, z), 0)) := by
    change (fun x : E2 => L.symm (x, z)) ''
      ((planar b).discChart '' Metric.sphere 0 1) = _
    rw [(planar b).discChart_image_sphere, ← range_comp]
    have hrec : (fun x : E2 => L.symm (x, z)) ∘ projected b =
        (fun theta => psi (leg b (theta, z), 0)) := by
      funext theta
      rw [htop b theta]
      exact heightPlaneCoordinates_reconstruct u (curve b theta) z (hcurveHeight b theta)
    rw [hrec]
  let W : SaddleLowerLevelData D :=
    { level := z
      level_lt_critical := by change c - delta < c; linarith
      lower_seams_lt_level := hseams
      label := label
      label_injective := hlabelInjective
      label_lower := hlabelLower
      leg := leg
      leg_source := hlegSource
      leg_smooth := hsmooth
      leg_inverse := hinverse
      leg_height := hheight
      leg_bottom := hbottom
      leg_disjoint := hlegDis 0 1 (by decide)
      leg_cover := hcover
      disc := disc
      disc_boundary := hdiscBoundary }
  exact ⟨W, rfl, htop, hlabelAll,
    SaddleLowerLevelData.disc_boundaries_disjoint W hpsi⟩

end PoincareConjecture.M25.Topology3D
