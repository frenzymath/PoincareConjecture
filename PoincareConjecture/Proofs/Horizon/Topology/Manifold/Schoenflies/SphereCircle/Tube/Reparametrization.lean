import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Radial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private def affineTubeTime (a b : Real) (hb : b ≠ 0) :
    Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ where
  toFun t := a + b * t
  invFun t := (t - a) / b
  left_inv t := by field_simp; ring
  right_inv t := by field_simp; ring
  contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const b).contMDiff

theorem exists_reparametrized_sphere_tube
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    {ε : Real} (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (a b : Real) (hb : b ≠ 0) {r : Real} (_hr : 0 < r)
    (hbound : |a| + |b| * r < ε) :
    ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-r) r ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      ∀ q t, F (q, t) = T (q, a + b * t) := by
  let TT : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { T with contMDiffOn_toFun := hT, contMDiffOn_invFun := hTi }
  let Q := (Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr (affineTubeTime a b hb)
  let P := Q.toPartialDiffeomorph.trans TT
  let W : Set (S1 × Real) := univ ×ˢ Ioo (-r) r
  have hW : IsOpen W := isOpen_univ.prod isOpen_Ioo
  have hWP : W ⊆ P.source := by
    intro z hz
    change z ∈ univ ∧ Q z ∈ T.source
    refine ⟨mem_univ _, ?_⟩
    rw [hsource]
    change z.1 ∈ univ ∧ a + b * z.2 ∈ Ioo (-ε) ε
    refine ⟨mem_univ _, abs_lt.mp ?_⟩
    calc
      |a + b * z.2| ≤ |a| + |b * z.2| := abs_add_le _ _
      _ = |a| + |b| * |z.2| := by rw [abs_mul]
      _ ≤ |a| + |b| * r := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (abs_lt.mpr hz.2).le (abs_nonneg _))
      _ < ε := hbound
  let F := P.toOpenPartialHomeomorph.restr W
  have hFs : F.source = W := by
    rw [show F.source = (P.toOpenPartialHomeomorph.restr W).source from rfl,
      OpenPartialHomeomorph.restr_source' _ W hW]
    exact inter_eq_right.mpr hWP
  have hFP : F.source ⊆ P.source := hFs ▸ hWP
  have hFt : F.target ⊆ P.target := by
    intro y hy
    exact F.right_inv hy ▸ P.map_source (hFP (F.map_target hy))
  exact ⟨F, hFs, P.contMDiffOn.mono hFP, P.symm.contMDiffOn.mono hFt, fun _ _ => rfl⟩

end Poincare.Manifold.Schoenflies
