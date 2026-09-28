import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.BoundaryReparametrization










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs

private theorem exists_matching_reparametrization
    (c d : UnitCircle → E2)
    (hc : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ c)
    (hd : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ d)
    (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hD : D '' range c = range d) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞,
      ∀ p, D (c p) = d (q p) := by
  obtain ⟨A, hA⟩ := exists_ambient_diffeomorph_of_smooth_circle c hc
  obtain ⟨qc, hqc⟩ := exists_planar_boundary_reparametrization c hc A hA
  have hAD : (A.trans D) '' sphere (0 : E2) 1 = range d := by
    change (D ∘ A) '' sphere (0 : E2) 1 = _
    rw [image_comp, hA, hD]
  obtain ⟨qd, hqd⟩ := exists_planar_boundary_reparametrization d hd (A.trans D) hAD
  refine ⟨qc.trans qd.symm, ?_⟩
  intro p
  change D (c p) = d (qd.symm (qc p))
  rw [← hqd, qd.apply_symm_apply]
  change D (c p) = D (A (qc p))
  rw [hqc]

private theorem supported_family_transport
    {a b : Real} {ι : Type*}
    (c d : ι → Real → UnitCircle → E2)
    (C D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hC : ContDiff Real ∞ (fun z : Real × E2 => C z.1 z.2))
    (hD : ContDiff Real ∞ (fun z : Real × E2 => D z.1 z.2))
    {KC KD K₀ : Set E2} (hKC : IsCompact KC) (hKD : IsCompact KD)
    (hK₀ : IsCompact K₀)
    (hCfix : ∀ t x, x ∉ KC → C t x = x)
    (hDfix : ∀ t x, x ∉ KD → D t x = x)
    (hCm : ∀ i t, t ∈ Icc a b → ∀ p, C t (c i a p) = c i t p)
    (hDm : ∀ i t, t ∈ Icc a b → ∀ p, D t (d i a p) = d i t p)
    (M : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hMfix : ∀ x, x ∉ K₀ → M x = x)
    (q : ι → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞)
    (hMq : ∀ i p, M (c i a p) = d i a (q i p)) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        ∀ t ∈ Icc a b, ∀ i p, Φ t (c i t p) = d i t (q i p) := by
  let Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => ((C t).symm.trans M).trans (D t)
  have hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) :=
    hD.comp (contDiff_fst.prodMk
      (M.contMDiff.contDiff.comp (contDiff_family_symm C hC)))
  refine ⟨KC ∪ K₀ ∪ KD, (hKC.union hK₀).union hKD, Φ, hΦ,
    contDiff_family_symm Φ hΦ, ?_, ?_⟩
  · intro t x hx
    have hCi : (C t).symm x = x := by
      apply (C t).injective
      exact ((C t).apply_symm_apply x).trans
        (hCfix t x (fun hy => hx (Or.inl (Or.inl hy)))).symm
    change D t (M ((C t).symm x)) = x
    rw [hCi, hMfix x (fun hy => hx (Or.inl (Or.inr hy))),
      hDfix t x (fun hy => hx (Or.inr hy))]
  · intro t ht i p
    change D t (M ((C t).symm (c i t p))) = d i t (q i p)
    rw [← hCm i t ht p, (C t).symm_apply_apply, hMq]
    exact hDm i t ht _



theorem exists_planar_circle_family_isotopy
    {a b : Real} (hab : a < b)
    (c d : Real → UnitCircle → E2)
    (hc : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × UnitCircle => c z.1 z.2))
    (hd : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × UnitCircle => d z.1 z.2))
    (hemb : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c t))
    (hemb' : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d t)) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞,
      ∃ K : Set E2, IsCompact K ∧
        ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
          (∀ t x, x ∉ K → Φ t x = x) ∧
          ∀ t ∈ Icc a b, ∀ p, Φ t (c t p) = d t (q p) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨KC, hKC, C, _, hC, _, hCfix, hCm⟩ :=
    exists_planar_circle_family_extension hab.le c hc hemb
  obtain ⟨KD, hKD, D, _, hD, _, hDfix, hDm⟩ :=
    exists_planar_circle_family_extension hab.le d hd hemb'
  obtain ⟨K₀, hK₀, M, hMfix, hM⟩ :=
    exists_supported_circle_matching (c a) (d a) (hemb a ha) (hemb' a ha)
  obtain ⟨q, hq⟩ :=
    exists_matching_reparametrization (c a) (d a) (hemb a ha) (hemb' a ha) M hM
  obtain ⟨K, hK, Φ, hΦ, hΦinv, hfix, hm⟩ :=
    supported_family_transport (fun (_ : Unit) => c) (fun (_ : Unit) => d)
      C D hC hD hKC hKD hK₀ hCfix hDfix (fun _ => hCm) (fun _ => hDm)
      M hMfix (fun _ => q) (fun _ => hq)
  exact ⟨q, K, hK, Φ, hΦ, hΦinv, hfix, fun t ht => hm t ht ()⟩




theorem exists_planar_circle_pair_family_isotopy
    {a b : Real} (hab : a < b)
    (c d : Fin 2 → Real → UnitCircle → E2)
    (hc : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × UnitCircle => c i z.1 z.2))
    (hd : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × UnitCircle => d i z.1 z.2))
    (hemb : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i t))
    (hemb' : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d i t))
    (hdisj : ∀ t ∈ Icc a b, Disjoint (range (c 0 t)) (range (c 1 t)))
    (hdisj' : ∀ t ∈ Icc a b, Disjoint (range (d 0 t)) (range (d 1 t)))
    (hnest : ∀ t ∈ Icc a b, ∀ i j, i ≠ j →
      (NestedPair (c i t) (c j t) ↔ NestedPair (d i t) (d j t))) :
    ∃ q : Fin 2 → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞,
      ∃ K : Set E2, IsCompact K ∧
        ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
          (∀ t x, x ∉ K → Φ t x = x) ∧
          ∀ t ∈ Icc a b, ∀ i p, Φ t (c i t p) = d i t (q i p) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨KC, hKC, C, _, hC, _, hCfix, hCm⟩ :=
    exists_planar_circle_pair_family_extension hab.le c hc hemb hdisj
  obtain ⟨KD, hKD, D, _, hD, _, hDfix, hDm⟩ :=
    exists_planar_circle_pair_family_extension hab.le d hd hemb' hdisj'
  obtain ⟨K₀, hK₀, M, hMfix, hM⟩ :=
    exists_supported_circle_pair_matching (fun i => c i a) (fun i => d i a)
      (fun i => hemb i a ha) (fun i => hemb' i a ha) (hdisj a ha) (hdisj' a ha)
      (hnest a ha)
  choose q hq using fun i => exists_matching_reparametrization
    (c i a) (d i a) (hemb i a ha) (hemb' i a ha) M (hM i)
  exact ⟨q, supported_family_transport c d C D hC hD hKC hKD hK₀
    hCfix hDfix hCm hDm M hMfix q hq⟩

end Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs
