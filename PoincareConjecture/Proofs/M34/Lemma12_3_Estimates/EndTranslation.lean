import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

def cylinderAxialTranslation (s : ℝ) (z : StandardCylinderSpace) : StandardCylinderSpace :=
  (z.1, z.2 + s)

theorem cylinderAxialTranslation_contMDiff (s : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (cylinderAxialTranslation s) :=
  contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)

set_option backward.isDefEq.respectTransparency false in

theorem cylinderAxialTranslation_mfderiv (s : ℝ) (z : StandardCylinderSpace)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialTranslation s) z v = v := by
  have hs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : StandardCylinderSpace => q.2 + s) z :=
    mdifferentiableAt_snd.add mdifferentiableAt_const
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : StandardCylinderSpace => q.2 + s) z =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z := by
    change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun q : StandardCylinderSpace => q.2 + s) z =
        mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Prod.snd z
    rw [mvfderiv_fun_add mdifferentiableAt_snd mdifferentiableAt_const,
      mvfderiv_const, add_zero]
  erw [cylinderAxialTranslation, mfderiv_prodMk mdifferentiableAt_fst hs,
    hd, mfderiv_fst, mfderiv_snd]
  rfl

variable {g : RiemannianMetric 3 StandardCapSpace}

def endAxialTranslation (e : StandardCylindricalEnd g) (s : ℝ)
    (x : StandardCapSpace) : StandardCapSpace :=
  e.coordinate (cylinderAxialTranslation s (e.inverse x))

theorem endAxialTranslation_coordinate (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 ≤ z.2) :
    endAxialTranslation e s (e.coordinate z) = e.coordinate (z.1, z.2 + s) := by
  rw [endAxialTranslation, e.coordinate_left_inverse ⟨mem_univ _, hz⟩]
  rfl

theorem endAxialTranslation_contMDiffAt (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < z.2 + s) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e s) (e.coordinate z) := by
  have hleft : e.inverse (e.coordinate z) = z :=
    e.coordinate_left_inverse ⟨mem_univ _, hz.le⟩
  have hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e.coordinate
      (cylinderAxialTranslation s (e.inverse (e.coordinate z))) := by
    rw [hleft]
    exact end_coordinate_contMDiffAt e hsz
  have ht : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (cylinderAxialTranslation s) (e.inverse (e.coordinate z)) :=
    (cylinderAxialTranslation_contMDiff s).contMDiffAt
  exact hc.comp (e.coordinate z) (ht.comp (e.coordinate z) (end_inverse_contMDiffAt e hz))

set_option backward.isDefEq.respectTransparency false in

theorem endAxialTranslation_mfderiv (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < z.2 + s)
    (u : TangentSpace (𝓡 3) (e.coordinate z)) :
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (e.coordinate z) u =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (z.1, z.2 + s)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u) := by
  have hleft : e.inverse (e.coordinate z) = z :=
    e.coordinate_left_inverse ⟨mem_univ _, hz.le⟩
  have hi := (end_inverse_contMDiffAt e hz).mdifferentiableAt (by simp)
  have hs := (cylinderAxialTranslation_contMDiff s).mdifferentiable (by simp)
  have hc : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
      (cylinderAxialTranslation s (e.inverse (e.coordinate z))) := by
    rw [hleft]
    exact (end_coordinate_contMDiffAt e hsz).mdifferentiableAt (by simp)
  change mfderiv (𝓡 3) (𝓡 3)
    (e.coordinate ∘ (cylinderAxialTranslation s ∘ e.inverse)) (e.coordinate z) u = _
  have ht : MDifferentiableAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialTranslation s ∘ e.inverse) (e.coordinate z) :=
    (hs (e.inverse (e.coordinate z))).comp (e.coordinate z) hi
  erw [mfderiv_comp (e.coordinate z) hc ht,
    mfderiv_comp (e.coordinate z) (hs (e.inverse (e.coordinate z))) hi]
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
    (cylinderAxialTranslation s (e.inverse (e.coordinate z)))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialTranslation s) (e.inverse (e.coordinate z))
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)) = _
  erw [cylinderAxialTranslation_mfderiv]
  congr 2
  exact congrArg (cylinderAxialTranslation s) hleft

set_option backward.isDefEq.respectTransparency false in

theorem endAxialTranslation_metric (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < z.2 + s)
    (u v : TangentSpace (𝓡 3) (e.coordinate z)) :
    g.inner (e.coordinate z) u v =
      g.inner (endAxialTranslation e s (e.coordinate z))
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (e.coordinate z) u)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (e.coordinate z) v) := by
  erw [endAxialTranslation_coordinate e s hz.le,
    endAxialTranslation_mfderiv e s hz hsz, endAxialTranslation_mfderiv e s hz hsz,
    e.metric_pullback _ hsz.le, end_inverse_metric e hz]
  rfl

theorem endAxialTranslation_local_isometry (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < z.2 + s) :
    ∃ U : Set StandardCapSpace, IsOpen U ∧ e.coordinate z ∈ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e s) U ∧
      ∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x,
        g.inner x u v = g.inner (endAxialTranslation e s x)
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x u)
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x v) := by
  let V : Set StandardCylinderSpace := univ ×ˢ Ioi (max 0 (-s))
  have hpos : ∀ w ∈ V, 0 < w.2 := fun _ hw => (le_max_left _ _).trans_lt hw.2
  have hshift : ∀ w ∈ V, 0 < w.2 + s := by
    intro w hw
    have h := (le_max_right 0 (-s)).trans_lt hw.2
    linarith
  refine ⟨e.coordinate '' V,
    end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioi) hpos,
    ⟨z, ⟨mem_univ _, max_lt_iff.mpr ⟨hz, by linarith⟩⟩, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have h := endAxialTranslation_contMDiffAt e s (hpos w hw) (hshift w hw)
    exact h.contMDiffWithinAt
  · rintro _ ⟨w, hw, rfl⟩ u v
    exact endAxialTranslation_metric e s (hpos w hw) (hshift w hw) u v

end PoincareConjecture.M34
