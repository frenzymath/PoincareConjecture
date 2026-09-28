import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Decomposition
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.PlanarTube

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

open _root_.M38Schoenflies.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

abbrev LowerCutIndex (A : AnnularEndFamily v g B C) :=
  {D : {D // D ∈ A.caps} // D.1.center < A.lowerCut}

abbrev UpperCutIndex (A : AnnularEndFamily v g B C) :=
  {D : {D // D ∈ A.caps} // A.upperCut < D.1.center}

instance (A : AnnularEndFamily v g B C) : Fintype A.LowerCutIndex := by
  classical
  infer_instance

instance (A : AnnularEndFamily v g B C) : Fintype A.UpperCutIndex := by
  classical
  infer_instance

def lowerCutCircle (A : AnnularEndFamily v g B C) (i : A.LowerCutIndex) : S1 → S2 :=
  fun q => (A.lower i.1.1 i.1.2 i.2).chart (q, A.lowerCut)

def upperCutCircle (A : AnnularEndFamily v g B C) (i : A.UpperCutIndex) : S1 → S2 :=
  fun q => (A.upper i.1.1 i.1.2 i.2).chart (q, A.upperCut)

theorem physical_middle_band_subset_core (A : AnnularEndFamily v g B C) :
    {p | inner Real v (g p) ∈ Icc A.lowerCut A.upperCut} ⊆ C := by
  intro p hp
  rw [A.core_complement]
  intro hcap
  obtain ⟨D, hD, x, hx, hxp⟩ := by simpa only [mem_iUnion, mem_image] using hcap
  have hout := A.cap_height_outside_middle D hD x (ball_subset_closedBall hx)
  rw [← D.parametrization_eq x (ball_subset_closedBall hx), hxp] at hout
  rcases hout with hl | hu
  · exact (not_lt_of_ge hp.1) hl
  · exact (not_lt_of_ge hp.2) hu

theorem lowerCutCircle_height (A : AnnularEndFamily v g B C)
    (i : A.LowerCutIndex) (q : S1) : inner Real v (g (A.lowerCutCircle i q)) = A.lowerCut :=
  (A.lower i.1.1 i.1.2 i.2).actual_height q A.lowerCut ⟨i.2.le, le_rfl⟩

theorem upperCutCircle_height (A : AnnularEndFamily v g B C)
    (i : A.UpperCutIndex) (q : S1) : inner Real v (g (A.upperCutCircle i q)) = A.upperCut :=
  (A.upper i.1.1 i.1.2 i.2).actual_height q A.upperCut ⟨le_rfl, i.2.le⟩

theorem lowerCutCircle_mem_end (A : AnnularEndFamily v g B C)
    (i : A.LowerCutIndex) (q : S1) : A.lowerCutCircle i q ∈ A.endRegion (.inl i) :=
  mem_image_of_mem _ ⟨mem_univ q, i.2.le, le_rfl⟩

theorem upperCutCircle_mem_end (A : AnnularEndFamily v g B C)
    (i : A.UpperCutIndex) (q : S1) : A.upperCutCircle i q ∈ A.endRegion (.inr i) := by
  change A.upperCutCircle i q ∈ (A.upper i.1.1 i.1.2 i.2).region
  rw [(A.upper i.1.1 i.1.2 i.2).region_eq_image]
  exact mem_image_of_mem _ ⟨mem_univ q, le_rfl, i.2.le⟩

theorem iUnion_range_lowerCutCircle (A : AnnularEndFamily v g B C) :
    (⋃ i, range (A.lowerCutCircle i)) = {p | inner Real v (g p) = A.lowerCut} := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, q, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hp
    exact A.lowerCutCircle_height i q
  · intro p hp
    have hpC := A.physical_middle_band_subset_core
      (show inner Real v (g p) ∈ Icc A.lowerCut A.upperCut by
        rw [hp]; exact ⟨le_rfl, A.cuts_lt.le⟩)
    have hph : A.height p = A.lowerCut := (A.height_germ p hpC).eq_of_nhds.trans hp
    have hcov := A.lower_cover.superset ⟨hpC, hph.le⟩
    obtain ⟨D, hD, hDc, ⟨q, t⟩, ⟨_, ht⟩, heq⟩ := by
      simpa only [mem_iUnion, LowerAnnularEnd.region, mem_image, mem_prod] using hcov
    have htc : t = A.lowerCut := by
      have hh := (A.lower D hD hDc).actual_height q t ht
      rw [heq, hp] at hh
      exact hh.symm
    exact mem_iUnion.mpr ⟨⟨⟨D, hD⟩, hDc⟩, q, by simpa [lowerCutCircle, htc] using heq⟩

theorem iUnion_range_upperCutCircle (A : AnnularEndFamily v g B C) :
    (⋃ i, range (A.upperCutCircle i)) = {p | inner Real v (g p) = A.upperCut} := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, q, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hp
    exact A.upperCutCircle_height i q
  · intro p hp
    have hpC := A.physical_middle_band_subset_core
      (show inner Real v (g p) ∈ Icc A.lowerCut A.upperCut by
        rw [hp]; exact ⟨A.cuts_lt.le, le_rfl⟩)
    have hph : A.height p = A.upperCut := (A.height_germ p hpC).eq_of_nhds.trans hp
    have hcov := A.upper_cover.superset ⟨hpC, hph.ge⟩
    obtain ⟨D, hD, hcD, hpD⟩ := by simpa only [mem_iUnion] using hcov
    rw [(A.upper D hD hcD).region_eq_image] at hpD
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, heq⟩ := hpD
    have htc : t = A.upperCut := by
      have hh := (A.upper D hD hcD).actual_height q t ht
      rw [heq, hp] at hh
      exact hh.symm
    exact mem_iUnion.mpr ⟨⟨⟨D, hD⟩, hcD⟩, q, by simpa [upperCutCircle, htc] using heq⟩

theorem annular_slice_geometry
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (t : Real) (ht : ∀ q, (q, t) ∈ F.source) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (fun q : S1 => F (q, t)) ∧
      Injective (fun q : S1 => F (q, t)) ∧
      ∀ q : S1, Injective (mfderiv (𝓡 1) (𝓡 2) (fun q : S1 => F (q, t)) q) := by
  let D : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { F with contMDiffOn_toFun := hF, contMDiffOn_invFun := hFi }
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact (hF.contMDiffAt (F.open_source.mem_nhds (ht q))).comp q
      ((contMDiff_id.prodMk contMDiff_const) q)
  · intro q q' heq
    exact congrArg Prod.fst (F.injOn (ht q) (ht q') heq)
  · intro q
    have hpair : MDifferentiableAt (𝓡 1) Iprod (fun q : S1 => (q, t)) q :=
      ((contMDiff_id (n := ∞)).prodMk (contMDiff_const (c := t)) q).mdifferentiableAt (by simp)
    have hloc : IsLocalDiffeomorphAt Iprod (𝓡 2) ∞ F (q, t) :=
      D.isLocalDiffeomorphAt Iprod (𝓡 2) ∞ (ht q)
    change Injective (mfderiv (𝓡 1) (𝓡 2) (F ∘ fun q : S1 => (q, t)) q)
    rw [mfderiv_comp q (hloc.contMDiffAt.mdifferentiableAt (by simp)) hpair]
    apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    change Injective (mfderiv (𝓡 1) Iprod
      (fun q : S1 => (id q, (fun _ : S1 => t) q)) q)
    rw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const,
      mfderiv_id, mfderiv_const]
    intro u w heq
    exact congrArg Prod.fst heq

theorem projected_circle_embedding
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (s : S1 → S2) (hs : ContMDiff (𝓡 1) (𝓡 2) ∞ s) (hsi : Injective s)
    (hsd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) s q))
    {c : Real} (hh : ∀ q, inner Real v (g (s q)) = c) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
      (fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (s q))) := by
  have hgs : ContMDiff (𝓡 1) (𝓡 3) ∞ (g ∘ s) := hg.contMDiff.comp hs
  have hgd (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (g ∘ s) q) := by
    rw [mfderiv_comp q (hg.contMDiff.mdifferentiable (by simp) (s q))
      (hs.mdifferentiable (by simp) q)]
    exact (injective_mfderiv_sphere_embedding hg (s q)).comp (hsd q)
  exact _root_.Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hgs)
    (_root_.Poincare.Geometry.Manifold.injective_projection_of_height_eq
      hv hh (hg.isEmbedding.injective.comp hsi))
    (_root_.Poincare.Geometry.Manifold.injective_mfderiv_projection_of_height_eq hv hgs hh hgd)

theorem lowerCutCircle_geometry (A : AnnularEndFamily v g B C) (i : A.LowerCutIndex) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (A.lowerCutCircle i) ∧ Injective (A.lowerCutCircle i) ∧
      ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) (A.lowerCutCircle i) q) := by
  let F := A.lower i.1.1 i.1.2 i.2
  apply annular_slice_geometry F.chart F.smooth F.symm_smooth A.lowerCut
  intro q
  rw [F.source]
  exact ⟨mem_univ _, by linarith [A.lower_lt, F.delta_pos], by linarith [F.delta_pos]⟩

theorem upperCutCircle_geometry (A : AnnularEndFamily v g B C) (i : A.UpperCutIndex) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (A.upperCutCircle i) ∧ Injective (A.upperCutCircle i) ∧
      ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) (A.upperCutCircle i) q) := by
  let F := A.upper i.1.1 i.1.2 i.2
  apply annular_slice_geometry F.chart F.smooth F.symm_smooth A.upperCut
  intro q
  rw [F.source]
  exact ⟨mem_univ _, by linarith [F.reflected.delta_pos],
    by linarith [A.upper_lt, F.reflected.delta_pos]⟩

theorem lowerCutCircle_isEmbedding (A : AnnularEndFamily v g B C) (i : A.LowerCutIndex) :
    Topology.IsEmbedding (A.lowerCutCircle i) :=
  ((A.lowerCutCircle_geometry i).1.continuous.isClosedEmbedding
    (A.lowerCutCircle_geometry i).2.1).isEmbedding

theorem upperCutCircle_isEmbedding (A : AnnularEndFamily v g B C) (i : A.UpperCutIndex) :
    Topology.IsEmbedding (A.upperCutCircle i) :=
  ((A.upperCutCircle_geometry i).1.continuous.isClosedEmbedding
    (A.upperCutCircle_geometry i).2.1).isEmbedding

theorem lowerCutCircle_projected_isSmoothEmbedding (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (i : A.LowerCutIndex) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
      (fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (A.lowerCutCircle i q))) :=
  projected_circle_embedding hg hv _ (A.lowerCutCircle_geometry i).1
    (A.lowerCutCircle_geometry i).2.1 (A.lowerCutCircle_geometry i).2.2 (A.lowerCutCircle_height i)

theorem upperCutCircle_projected_isSmoothEmbedding (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (i : A.UpperCutIndex) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
      (fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (A.upperCutCircle i q))) :=
  projected_circle_embedding hg hv _ (A.upperCutCircle_geometry i).1
    (A.upperCutCircle_geometry i).2.1 (A.upperCutCircle_geometry i).2.2 (A.upperCutCircle_height i)

theorem lowerCutCircle_joint_injective (A : AnnularEndFamily v g B C) :
    Injective (fun z : A.LowerCutIndex × S1 => A.lowerCutCircle z.1 z.2) := by
  rintro ⟨i, q⟩ ⟨j, z⟩ heq
  change A.lowerCutCircle i q = A.lowerCutCircle j z at heq
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (A.pairwise_disjoint (fun h => hne (Sum.inl.inj h)))
      (A.lowerCutCircle_mem_end i q) (heq.symm ▸ A.lowerCutCircle_mem_end j z)
  subst j
  exact Prod.ext rfl ((A.lowerCutCircle_geometry i).2.1 heq)

theorem upperCutCircle_joint_injective (A : AnnularEndFamily v g B C) :
    Injective (fun z : A.UpperCutIndex × S1 => A.upperCutCircle z.1 z.2) := by
  rintro ⟨i, q⟩ ⟨j, z⟩ heq
  change A.upperCutCircle i q = A.upperCutCircle j z at heq
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (A.pairwise_disjoint (fun h => hne (Sum.inr.inj h)))
      (A.upperCutCircle_mem_end i q) (heq.symm ▸ A.upperCutCircle_mem_end j z)
  subst j
  exact Prod.ext rfl ((A.upperCutCircle_geometry i).2.1 heq)

theorem lowerCutCircle_projected_joint_injective (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1) :
    Injective (fun z : A.LowerCutIndex × S1 =>
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (A.lowerCutCircle z.1 z.2))) := by
  intro z y heq
  apply A.lowerCutCircle_joint_injective
  apply hg
  apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
  exact Prod.ext ((A.lowerCutCircle_height z.1 z.2).trans
    (A.lowerCutCircle_height y.1 y.2).symm) heq

theorem upperCutCircle_projected_joint_injective (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1) :
    Injective (fun z : A.UpperCutIndex × S1 =>
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (A.upperCutCircle z.1 z.2))) := by
  intro z y heq
  apply A.upperCutCircle_joint_injective
  apply hg
  apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
  exact Prod.ext ((A.upperCutCircle_height z.1 z.2).trans
    (A.upperCutCircle_height y.1 y.2).symm) heq

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

end

end M38Schoenflies
