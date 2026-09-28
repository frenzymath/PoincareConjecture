import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarShellMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (0 : ℝ) (1/8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7/8) 1

theorem exists_original_signed_collar_shell
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} (c : V3 × ℝ → X)
    (hc : PolyhedralPLInCharts e c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (Q : (Sphere ×ˢ J : Set (V3 × ℝ)) ≃ₜ T) (f : V3 → X),
      Q.IsFinitePL ∧
      (∀ z : (Sphere ×ˢ J : Set (V3 × ℝ)), ‖(Q z : V3)‖ = 1-(z : V3 × ℝ).2) ∧
      PolyhedralPLInCharts e f T ∧ InjOn f T ∧
      f '' T = c '' (Sphere ×ˢ Icc (-δ) δ) ∧
      ∀ z : (Sphere ×ˢ J : Set (V3 × ℝ)),
        f (Q z) = c ((z : V3 × ℝ).1,16*δ*(z : V3 × ℝ).2-δ) := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := isFinitePLBallPair_Icc zero_lt_one
  let a : ℝ →ᴬ[ℝ] ℝ :=
    (2*δ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ δ
  have haval (t : ℝ) : a t = 2*δ*t-δ := rfl
  have ha : FinitePiecewiseAffineOn a I := ⟨L,hL,hLs,L.affineOnFaces_affine a⟩
  have hid : FinitePiecewiseAffineOn (id : V3 → V3) K.space :=
    ⟨K,hK,rfl,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩
  have hprod : FinitePiecewiseAffineOn (Prod.map id a) (K.space ×ˢ I) := hid.prodMap ha
  have hmaps (z : V3 × ℝ) (hz : z ∈ K.space ×ˢ I) :
      Prod.map id a z ∈ Sphere ×ˢ Icc (-1 : ℝ) 1 := by
    refine ⟨hKs.subset hz.1,?_,?_⟩ <;> dsimp [a] <;> nlinarith [hz.2.1,hz.2.2]
  let d := c ∘ Prod.map id a
  have hd : PolyhedralPLInCharts e d (K.space ×ˢ I) := by
    obtain ⟨M,hM,hMs,hfaces⟩ := hprod
    rw [←hMs]
    exact hc.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hfaces⟩
      (fun z hz => hmaps z (hMs.subset hz))
  have hdi : InjOn d (K.space ×ˢ I) := by
    intro z hz w hw hzw
    have h := hci (hmaps z hz) (hmaps w hw) hzw
    apply Prod.ext
    · simpa only [Prod.map_fst,id_eq] using congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    change a z.2 = a w.2 at ht
    rw [haval,haval] at ht
    nlinarith
  have hcompact : IsCompact (K.space ×ˢ I) := (K.isCompact_space_of_finite hK).prod isCompact_Icc
  let : CompactSpace (K.space ×ˢ I : Set (V3 × ℝ)) := isCompact_iff_compactSpace.mp hcompact
  have hemb : Topology.IsEmbedding (fun z : (K.space ×ˢ I : Set (V3 × ℝ)) => d z) :=
    (hd.continuousOn.domRestrict.isClosedEmbedding
      (fun z w h => Subtype.ext (hdi z.property w.property h))).isEmbedding
  let q := Homeomorph.setCongr hKs.symm
  have hq : q.IsFinitePL :=
    ⟨id,⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩,fun _ => rfl⟩
  obtain ⟨Q,hQ,_,hQnorm,_⟩ := exists_unitCube_inward_finitePL_collar
  obtain ⟨f,hf,hfi,himage,hvalue⟩ := exists_original_collar_shell_map K d hd hemb q hq Q hQ
    (show (0 : ℝ) < 1 by norm_num) (le_refl 1)
  refine ⟨Q,f,hQ,hQnorm,hf,hfi,?_,?_⟩
  · rw [himage]
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨(z.1,a z.2),⟨hKs.subset hz.1,?_,?_⟩,rfl⟩ <;>
        rw [haval] <;> nlinarith [hz.2.1,hz.2.2]
    · rintro _ ⟨z,hz,rfl⟩
      let u := (z.2+δ)/(2*δ)
      have hu : u ∈ I := ⟨div_nonneg (by linarith [hz.2.1]) (by positivity),
        (div_le_iff₀ (by positivity : 0 < 2*δ)).mpr (by linarith [hz.2.2])⟩
      refine ⟨(z.1,u),⟨hKs.symm.subset hz.1,hu⟩,?_⟩
      change c (z.1,a u) = c z
      congr 1
      apply Prod.ext
      · rfl
      rw [haval]
      dsimp [u]
      field_simp
      ring
  · intro z
    rw [hvalue]
    change c ((z : V3 × ℝ).1,a (8*1*(z : V3 × ℝ).2)) = _
    congr 1
    apply Prod.ext
    · rfl
    rw [haval]
    ring

end PoincareConjecture.M76
