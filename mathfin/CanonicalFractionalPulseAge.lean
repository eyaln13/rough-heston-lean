import CanonicalCompanionBoundary
import FractionalPulseBirthConditioning
import PositiveClusterMass

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The filtration seen at deterministic ages after the pulse birth. -/
def pulseAgeFiltration (𝒢 : Filtration ℝ≥0 m) (τ : ℝ≥0) : Filtration ℝ≥0 m :=
  ⟨fun t => 𝒢 (τ+t),fun _ _ hst => 𝒢.mono (add_le_add_right hst τ),fun t => 𝒢.le (τ+t)⟩

theorem martingale_pulseAgeFiltration {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0→Ω→ℝ} (hM : Martingale M 𝒢 μ) (τ : ℝ≥0) :
    Martingale (fun t => M (τ+t)) (pulseAgeFiltration 𝒢 τ) μ :=
  martingale_of_past_set_integrals (fun t => hM.stronglyAdapted (τ+t))
    (fun t => hM.integrable (τ+t))
    (fun _ _ hst _ hA => hM.setIntegral_eq (add_le_add_right hst τ) hA)

/-- Physical pulse immigration at birth time τ. -/
noncomputable def translatedPulseRate (τ : ℝ≥0) (ε d : ℝ) (t : ℝ≥0) : ℝ :=
  rectangularPulseRate ε d ((t:ℝ)-(τ:ℝ))

theorem translatedPulseRate_measurable (τ : ℝ≥0) (ε d : ℝ) :
    Measurable (translatedPulseRate τ ε d) :=
  ((measurable_const (a := ε/d)).indicator measurableSet_Ioc).comp
    ((continuous_sub_right (τ:ℝ)).measurable.comp NNReal.continuous_coe.measurable)

theorem norm_translatedPulseRate_le (τ : ℝ≥0) (ε d : ℝ) (t : ℝ≥0) :
    ‖translatedPulseRate τ ε d t‖≤‖ε/d‖ := by
  unfold translatedPulseRate rectangularPulseRate
  by_cases ht : (t:ℝ)-(τ:ℝ)∈Ioc (0:ℝ) d
  · simp [Set.indicator_of_mem ht]
  · simpa only [Set.indicator_of_notMem ht,norm_zero] using norm_nonneg (ε/d)

private theorem pulse_fold_singular_history {α τ r : ℝ} (hα' : α<1)
    (hτ : 0≤τ) (hr : 0≤r) {V : ℝ→ℝ} (hVc : Continuous V)
    (hV0 : EqOn V 0 (Icc (0:ℝ) τ)) :
    volterraConvolution (fractionalL α) V (τ+r) =
      volterraConvolution (fractionalL α) (fun u => V (τ+u)) r := by
  let f (s : ℝ) := fractionalL α (τ+r-s)*V s
  have hτr : 0≤τ+r := add_nonneg hτ hr
  have hτle : τ≤τ+r := le_add_of_nonneg_right hr
  have hf : IntegrableOn f (Ioc 0 (τ+r)) :=
    (cluster_affine_payoff_integrability_of_continuous hα' hτr hVc).2
  have hfi : IntervalIntegrable f volume 0 (τ+r) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτr).2 hf
  have hpre : (∫ u in (0:ℝ)..τ,f u)=0 := by
    rw [intervalIntegral.integral_of_le hτ]
    exact setIntegral_eq_zero_of_forall_eq_zero (fun u hu => by
      dsimp [f]
      rw [hV0 (Ioc_subset_Icc_self hu)]
      simp only [Pi.zero_apply,mul_zero])
  have hadde := intervalIntegral.integral_add_adjacent_intervals
    (hfi.mono_set (by rw [uIcc_of_le hτ,uIcc_of_le hτr]; exact Icc_subset_Icc_right hτle))
    (hfi.mono_set (by rw [uIcc_of_le hτle,uIcc_of_le hτr]; exact Icc_subset_Icc_left hτ))
  rw [hpre,zero_add] at hadde
  change (∫ u in Ioc (0:ℝ) (τ+r),f u)=∫ u in Ioc (0:ℝ) r,fractionalL α (r-u)*V (τ+u)
  rw [← intervalIntegral.integral_of_le hτr,← intervalIntegral.integral_of_le hr,← hadde]
  rw [← show (∫ u in (0:ℝ)..r,f (τ+u)) = ∫ u in τ..τ+r,f u by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := r) f τ]
  congr 1
  funext u
  dsimp [f]
  rw [show τ+r-(τ+u)=r-u by ring]

private theorem pulse_shift_regular_integral {τ r : ℝ} (hτ : 0≤τ) (hr : 0≤r)
    {f : ℝ→ℝ} (hf : IntegrableOn f (Ioc 0 (τ+r)))
    (hpre : ∀ u∈Ioc (0:ℝ) τ,f u=0) :
    (∫ u in (0:ℝ)..τ+r,f u)=∫ u in (0:ℝ)..r,f (τ+u) := by
  have hτr := add_nonneg hτ hr
  have hτle : τ≤τ+r := le_add_of_nonneg_right hr
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hτr).2 hf
  have hzero : (∫ u in (0:ℝ)..τ,f u)=0 := by
    rw [intervalIntegral.integral_of_le hτ]
    exact setIntegral_eq_zero_of_forall_eq_zero hpre
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (by rw [uIcc_of_le hτ,uIcc_of_le hτr]; exact Icc_subset_Icc_right hτle))
    (hi.mono_set (by rw [uIcc_of_le hτle,uIcc_of_le hτr]; exact Icc_subset_Icc_left hτ))
  rw [hzero,zero_add] at hadd
  rw [← hadd]
  simpa only [add_zero] using
    (intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := r) f τ).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "𝒢" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- Before birth, a zero-initial pulse row is identically zero on a single
full-measure set. This is obtained from positivity of inverse history and the
zero mean of the physical residual at birth. -/
theorem canonical_pulse_zero_through_birth
    {α κ ε d : ℝ} (hα' : α<1) (hκ : 0≤κ)
    {v : Option ι→ℝ} {i : ι} (hv : v (some i)=0)
    (P : ProbabilityMeasure Path)
    (hI : ∀ᵐ p ∂(P:Measure Path),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Path),p∈canonicalPhysicalNonnegative (ι := ι) T)
    {τ : ℝ≥0} (hτT : τ≤T)
    (hInv : ∀ᵐ p ∂(P:Measure Path),∀ t≤T,
      volterraConvolution (fractionalL α) (fun r => canonicalPhysicalVariance T (some i) r.toNNReal p-v (some i)) (t:ℝ) =
        canonicalPhysicalResidual T (some i) t p +
          ∫ r in (0:ℝ)..(t:ℝ),translatedPulseRate τ ε d r.toNNReal-κ*canonicalPhysicalVariance T (some i) r.toNNReal p)
    (hM : Martingale (canonicalPhysicalResidual T (some i)) 𝒢 (P:Measure Path)) :
    ∀ᵐ p ∂(P:Measure Path), (∀ u≤τ,canonicalRegularVariance T (some i) (v (some i)) u p=0) ∧
      canonicalPhysicalResidual T (some i) τ p=0 := by
  let μ := (P:Measure Path)
  let V := canonicalRegularVariance T (some i) (v (some i))
  let M := canonicalPhysicalResidual T (some i)
  obtain ⟨hVc,hVn,hV0⟩ :=
    canonicalRegularVariance_continuous_nonnegative_initial (T := T) (v := v (some i)) (some i) (by rw [hv])
  have hM0 := canonicalPhysicalResidual_zero_ae hI (some i)
  rcases eq_or_lt_of_le (show (0:ℝ≥0)≤τ from zero_le) with hτ0|hτpos
  · subst τ
    filter_upwards [hM0] with p hp
    exact ⟨fun u hu => (congrArg (fun s => V s p) (le_antisymm hu zero_le)).trans ((hV0 p).trans hv),hp⟩
  have hτp : (0:ℝ)<τ := NNReal.coe_pos.mpr hτpos
  have hτl : (τ:ℝ)≤T := NNReal.coe_le_coe.mpr hτT
  have heq := canonicalRegularVariance_inverse_ae_of_centered hα' P hI hN (some i)
    (translatedPulseRate_measurable τ ε d) (norm_translatedPulseRate_le τ ε d) hInv
  have hsplit : ∀ᵐ p ∂μ, M τ p =
      volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) τ +
        ∫ u in Ioc (0:ℝ) (τ:ℝ),κ*V u.toNNReal p := by
    filter_upwards [heq] with p hp
    have he := hp (τ:ℝ) ⟨hτp,hτl⟩
    rw [Real.toNNReal_coe] at he
    refine he.trans (congrArg (fun x : ℝ => volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) τ + x) ?_)
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hu' : ((u.toNNReal:ℝ≥0):ℝ)-(τ:ℝ) ∉ Ioc (0:ℝ) d := by
      rw [Real.coe_toNNReal u hu.1.le]
      exact fun h => (not_lt_of_ge (sub_nonpos.mpr hu.2)) h.1
    change κ*V u.toNNReal p - (translatedPulseRate τ ε d u.toNNReal + v (some i)*fractionalL α u) = κ*V u.toNNReal p
    simp only [hv,zero_mul,add_zero,translatedPulseRate,rectangularPulseRate,Set.indicator_of_notMem hu',sub_zero]
  have hLnn (p : Path) :
      0≤volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) τ := by
    unfold volterraConvolution fractionalL
    apply integral_nonneg
    intro u
    apply mul_nonneg _ (hVn _ _)
    split
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.Gamma_nonneg_of_nonneg (by linarith))
  have hDnn (p : Path) : 0≤∫ u in Ioc (0:ℝ) (τ:ℝ),κ*V u.toNNReal p :=
    integral_nonneg fun u => mul_nonneg hκ (hVn _ _)
  have hMnn : 0≤ᵐ[μ] M τ := hsplit.mono fun p hp => hp ▸ add_nonneg (hLnn p) (hDnn p)
  have hMmean := hM.setIntegral_eq (show (0:ℝ≥0)≤τ from zero_le) MeasurableSet.univ
  rw [Measure.restrict_univ,integral_congr_ae hM0,integral_zero] at hMmean
  have hMτ := (integral_eq_zero_iff_of_nonneg_ae hMnn (hM.integrable τ)).mp hMmean.symm
  filter_upwards [hsplit,hMτ] with p hp hz
  refine ⟨?_,hz⟩
  have hmz : M τ p=0 := hz
  have hL0 : volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) τ=0 := by
    linarith only [hp,hmz,hLnn p,hDnn p]
  have hinner : EqOn (fun u : ℝ => V u.toNNReal p) 0 (Ioo (0:ℝ) (τ:ℝ)) := by
    intro u hu
    by_contra! h
    have hpos : 0<V u.toNNReal p := lt_of_le_of_ne (hVn _ _) (Ne.symm h)
    have hLc := fractional_cluster_history_pos hα' hu ((hVc p).comp continuous_real_toNNReal)
      (fun u _ => hVn _ _) hpos
    exact (ne_of_gt hLc) hL0
  have hclosed := hinner.closure ((hVc p).comp continuous_real_toNNReal) continuous_const
  rw [closure_Ioo hτp.ne] at hclosed
  intro u hu
  simpa only [Real.toNNReal_coe,Pi.zero_apply] using
    hclosed ⟨u.coe_nonneg,NNReal.coe_le_coe.mpr hu⟩

/-- A version of the age process with every path zero at age zero. The
modification is determined by the birth-time information. -/
noncomputable def canonicalPulseAgeVariance (T τ : ℝ≥0) (i : ι) (v : ℝ)
    (t : ℝ≥0) (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  if canonicalRegularVariance T (some i) v τ p=0 then
    canonicalRegularVariance T (some i) v (τ+t) p else 0

private theorem canonicalPulseAgeVariance_adapted (τ : ℝ≥0) (i : ι) (v : ℝ) :
    StronglyAdapted (pulseAgeFiltration 𝒢 τ) (canonicalPulseAgeVariance T τ i v) := by
  intro t
  change StronglyMeasurable[𝒢 (τ+t)] (canonicalPulseAgeVariance T τ i v t)
  have hV := canonicalRegularVariance_adapted (T := T) (some i) v
  have hτ := ((hV τ).mono ((𝒢).mono (le_add_of_nonneg_right (show 0≤t from zero_le)))).measurable
  exact ((hV (τ+t)).measurable.ite (measurableSet_eq_fun hτ measurable_const)
    measurable_const).stronglyMeasurable

/-- A zero-initial physical coordinate with translated rectangular input is
the actual fractional pulse in the common filtration shifted to its birth. -/
theorem canonicalFractionalPulse_at_age
    {α κ σ ε d : ℝ} (hα' : α<1) (hκ : 0≤κ)
    {v : Option ι→ℝ} {i : ι} (hv : v (some i)=0)
    (P : ProbabilityMeasure Path)
    (hI : ∀ᵐ p ∂(P:Measure Path),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Path),p∈canonicalPhysicalNonnegative (ι := ι) T)
    {τ : ℝ≥0} (hτT : τ≤T)
    (hInv : ∀ᵐ p ∂(P:Measure Path),∀ t≤T,
      volterraConvolution (fractionalL α) (fun r => canonicalPhysicalVariance T (some i) r.toNNReal p-v (some i)) (t:ℝ) =
        canonicalPhysicalResidual T (some i) t p +
          ∫ r in (0:ℝ)..(t:ℝ),translatedPulseRate τ ε d r.toNNReal-κ*canonicalPhysicalVariance T (some i) r.toNNReal p)
    (hM : Martingale (canonicalPhysicalResidual T (some i)) 𝒢 (P:Measure Path))
    (hM₂ : ∀ t,MemLp (canonicalPhysicalResidual T (some i) t) 2 (P:Measure Path))
    (hC : Martingale (canonicalPhysicalCompensatedProduct T σ (some i) (some i)) 𝒢 (P:Measure Path)) :
    FractionalPulseProcess (P:Measure Path) (pulseAgeFiltration 𝒢 τ) (T-τ)
      α κ (σ^2/2) ε d (fun t => canonicalPhysicalResidual T (some i) (τ+t))
      (canonicalPulseAgeVariance T τ i (v (some i)))
      (fun t => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t)) := by
  let μ := (P:Measure Path)
  let V := canonicalRegularVariance T (some i) (v (some i))
  let U := canonicalPulseAgeVariance T τ i (v (some i))
  let M := canonicalPhysicalResidual T (some i)
  have hpre := canonical_pulse_zero_through_birth hα' hκ hv P hI hN hτT hInv hM
  obtain ⟨hVc,hVn,_⟩ :=
    canonicalRegularVariance_continuous_nonnegative_initial (T := T) (v := v (some i))
      (some i) (hv.symm ▸ le_rfl)
  have hUa : ∀ᵐ p ∂μ,∀ t,U t p=V (τ+t) p := by
    filter_upwards [hpre] with p hp t
    change (if V τ p=0 then V (τ+t) p else 0)=V (τ+t) p
    rw [ite_eq_left (hp.1 τ le_rfl)]
  have hUzero (p : Path) : U 0 p=0 := by
    change (if V τ p=0 then V (τ+0) p else 0)=0
    rw [add_zero]
    split <;> first | assumption | rfl
  have hUc (p : Path) : Continuous (fun t => U t p) := by
    by_cases hp : V τ p=0
    · have he (t : ℝ≥0) : U t p=V (τ+t) p := by
        change (if V τ p=0 then V (τ+t) p else 0)=V (τ+t) p
        rw [ite_eq_left hp]
      exact ((hVc p).comp (continuous_const.add continuous_id)).congr fun t => (he t).symm
    · have he (t : ℝ≥0) : U t p=0 := by
        change (if V τ p=0 then V (τ+t) p else 0)=0
        rw [ite_eq_right hp]
      exact (continuous_const : Continuous (fun _ : ℝ≥0 => (0:ℝ))).congr fun t => (he t).symm
  have hUn (t : ℝ≥0) (p : Path) : 0≤U t p := by
    unfold U canonicalPulseAgeVariance
    split
    · exact hVn _ _
    · exact le_rfl
  have hτ : 0≤(τ:ℝ) := NNReal.coe_nonneg _
  have htoNN (r : ℝ) (hr : 0≤r) : ((τ:ℝ)+r).toNNReal = τ+r.toNNReal := by
    rw [Real.toNNReal_add hτ hr,Real.toNNReal_coe]
  have hτplus (t : ℝ≥0) (ht : t≤T-τ) : τ+t≤T := by
    calc
      _ ≤ τ+(T-τ) := add_le_add_right ht τ
      _ = T := add_tsub_cancel_of_le hτT
  refine ⟨martingale_pulseAgeFiltration hM τ,(fun t => hM₂ (τ+t)),
    (fun p => (canonicalPhysicalResidual_time_continuous (some i) p).comp
      (continuous_const.add continuous_id)),?_,
    canonicalPulseAgeVariance_adapted τ i _,hUc,hUn,hUzero,
    martingale_pulseAgeFiltration hC τ,
    (fun t => canonicalPhysical_diagonal_clock_integrable σ (some i) hM₂ hC (τ+t)),
    ?_,?_,?_⟩
  · filter_upwards [hpre] with p hp
    simpa only [add_zero] using hp.2
  · intro s t hst
    exact ae_of_all _ fun p => canonicalPhysical_diagonal_monotone σ (some i) p (add_le_add_right hst τ)
  · intro t ht
    filter_upwards [canonicalPhysical_diagonal_clock_regular_ae hI hN σ (some i),hpre,hUa] with p hCp hVp hUp
    change canonicalPhysicalCompensator T σ (some i) (some i) (τ+t) p = ∫ r in (0:ℝ)..(t:ℝ),(2*(σ^2/2))*U r.toNNReal p
    let f (r : ℝ) := σ^2*V r.toNNReal p
    have hf : Continuous f := continuous_const.mul ((hVc p).comp continuous_real_toNNReal)
    have hfI : IntegrableOn f (Ioc (0:ℝ) ((τ:ℝ)+(t:ℝ))) :=
      (hf.intervalIntegrable 0 _).1
    have hzero (u : ℝ) (hu : u ∈ Ioc (0:ℝ) (τ:ℝ)) : f u=0 := by
      change σ^2*V u.toNNReal p=0
      have hz : V u.toNNReal p=0 := hVp.1 _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      rw [hz,mul_zero]
    rw [hCp (τ+t) (hτplus t ht),show (∫ r in (0:ℝ)..(((τ+t:ℝ≥0):ℝ)),σ^2 * canonicalRegularVariance T (some i) (v (some i)) r.toNNReal p) =
      ∫ r in (0:ℝ)..((τ:ℝ)+(t:ℝ)),f r by rw [NNReal.coe_add],
      show 2*(σ^2/2)=σ^2 by ring,
      pulse_shift_regular_integral hτ (NNReal.coe_nonneg t) hfI hzero]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hr
    change σ^2*V ((τ:ℝ)+r).toNNReal p = σ^2*U r.toNNReal p
    rw [htoNN r hr.1,hUp]
  · have heq := canonicalRegularVariance_inverse_ae_of_centered hα' P hI hN (some i)
      (translatedPulseRate_measurable τ ε d) (norm_translatedPulseRate_le τ ε d) hInv
    filter_upwards [heq,hpre,hUa] with p hp hVp hUp
    intro r hr
    have hrt : r.toNNReal≤T-τ := Real.toNNReal_le_iff_le_coe.mpr hr.2
    have hu : (τ:ℝ)+r∈Ioc (0:ℝ) (T:ℝ) := by
      refine ⟨add_pos_of_nonneg_of_pos hτ hr.1,?_⟩
      simpa only [NNReal.coe_add,Real.coe_toNNReal _ hr.1.le] using
        NNReal.coe_le_coe.mpr (hτplus r.toNNReal hrt)
    have hh := hp ((τ:ℝ)+r) hu
    rw [htoNN r hr.1.le] at hh
    have hterm (u : ℝ) : v (some i)*fractionalL α u=0 := by rw [hv,zero_mul]
    simp only [hterm,add_zero] at hh
    change canonicalPhysicalResidual T (some i) (τ+r.toNNReal) p =
      volterraConvolution (fractionalL α) (fun u => U u.toNNReal p) r +
        ∫ u in Ioc (0:ℝ) r,κ*U u.toNNReal p-rectangularPulseRate ε d u
    change (canonicalPhysicalResidual T (some i) (τ+r.toNNReal) p =
      volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) ((τ:ℝ)+r) +
      ∫ u in Ioc (0:ℝ) ((τ:ℝ)+r),κ*V u.toNNReal p-translatedPulseRate τ ε d u.toNNReal) at hh
    have hfold : volterraConvolution (fractionalL α) (fun u => V u.toNNReal p) ((τ:ℝ)+r) =
        volterraConvolution (fractionalL α) (fun u => V ((τ:ℝ)+u).toNNReal p) r :=
      pulse_fold_singular_history hα' hτ hr.1.le
        ((hVc p).comp continuous_real_toNNReal)
        (fun u hu => hVp.1 _ (Real.toNNReal_le_iff_le_coe.mpr hu.2))
    rw [hh,hfold]
    congr 1
    · unfold volterraConvolution
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change fractionalL α (r-u)*V ((τ:ℝ)+u).toNNReal p = fractionalL α (r-u)*U u.toNNReal p
      rw [htoNN u hu.1.le,hUp]
    · let f (u : ℝ) := κ*V u.toNNReal p- translatedPulseRate τ ε d u.toNNReal
      have hfI : IntegrableOn f (Ioc (0:ℝ) ((τ:ℝ)+r)) := by
        refine (((continuous_const.mul ((hVc p).comp continuous_real_toNNReal)).intervalIntegrable 0 _).1).sub ?_
        refine (integrableOn_const (C := ‖ε/d‖)
          (by simp [Real.volume_Ioc] : volume (Ioc (0:ℝ) ((τ:ℝ)+r))≠∞)).mono'
          ((translatedPulseRate_measurable τ ε d).comp continuous_real_toNNReal.measurable).aestronglyMeasurable ?_
        exact ae_of_all _ fun u => norm_translatedPulseRate_le τ ε d u.toNNReal
      have hfz (u : ℝ) (hu : u∈Ioc (0:ℝ) (τ:ℝ)) : f u=0 := by
        have hvz : V u.toNNReal p=0 := hVp.1 u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
        have hbz : ((u.toNNReal:ℝ≥0):ℝ)-(τ:ℝ)∉Ioc (0:ℝ) d := by
          rw [Real.coe_toNNReal u hu.1.le]
          exact fun h => (not_lt_of_ge (sub_nonpos.mpr hu.2)) h.1
        change κ*V u.toNNReal p-translatedPulseRate τ ε d u.toNNReal=0
        simp only [hvz,mul_zero,translatedPulseRate,rectangularPulseRate,Set.indicator_of_notMem hbz,sub_zero]
      change (∫ u in Ioc (0:ℝ) ((τ:ℝ)+r),f u) = _
      rw [← intervalIntegral.integral_of_le hu.1.le,← intervalIntegral.integral_of_le hr.1.le,
        pulse_shift_regular_integral hτ hr.1.le hfI hfz]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hr.1.le] at hu
      have h0 : 0≤(τ:ℝ)+u := add_nonneg hτ hu.1
      change κ*V ((τ:ℝ)+u).toNNReal p - translatedPulseRate τ ε d ((τ:ℝ)+u).toNNReal =
        κ*U u.toNNReal p-rectangularPulseRate ε d u
      rw [hUp,← htoNN u hu.1,translatedPulseRate,Real.coe_toNNReal _ h0]
      congr 2
      ring

#print axioms martingale_pulseAgeFiltration
#print axioms canonical_pulse_zero_through_birth
#print axioms canonicalFractionalPulse_at_age

end RoughHeston
