class HMM
  attr_reader :transition, :emission, :initial_probs

  def initialize(trans, emiss, init)
    @transition = trans
    @emission = emiss
    @initial_probs = init
  end

  # forward_backward : List Observation -> ObsNumber -> State -> Probability
  def forward_backward(observations)
    # p(x_k|o_1:t) = p(x_k,o_1:t) / p(o_1:t)
    #              = p(x_k, o_1:k, o_k+1:t) / p(o_1:t)
    #              = p(x_k, o_1:k)p(o_k+1:t|x_k,o_1:k) / p(o_1:t)
    #              = p(x_k, o_1:k)p(o_k+1:t|x_k) / p(o_1:t)

    forward = compute_forward observations
    backward = compute_backward observations

    denom = forward[observations.length - 1].inject :+

    (0...observations.length).map { |obs_num|
      (0...num_states).map { |state| forward[obs_num][state] * backward[obs_num][state] / denom}
    }
  end

  def compute_backward(observations)
    # b[k] = p(o_k+1:t|x_k)
    b = (0...observations.length).map { Array.new num_states }

    b[observations.length - 1] = [1]*num_states

    # b[k] = p(o_k+1:t | x_k)
    #      = Sum p(x_k+1, o_k+1, o_k+2:t | x_k)
    #      = Sum p(o_k+1|x_k+1) * p(x_k+1|x_k) * p(x_k+2:t|x_k+1)
    #      = Sum p(o_k+1|x_k+1) * p(x_k+1|x_k) * b[k+1][x_k+1]
    (observations.length - 2).downto(0) do |k|
      (0...num_states).each do |state|
        b[k][state] = b[k+1].map.with_index do |b, i|
          b * transition[state][i] * emission[i][observations[k+1]]
        end.inject(:+)
      end
    end

    b
  end

  def compute_forward(observations)
    # a[k] = p(x_k,o_1:k)
    a = (0...observations.length).map { Array.new num_states }

    # a[0] = p(x_0,o_0) = p(o_0|x_0)*p(x_0)
    a[0] =
      (0...num_states).map { |state| emission[state][observations[0]] * initial_probs[state] }

    # a[k] = p(x_k,o_1:k)
    #      = Sum p(x_k, x_k-1, o_1:k-1, o_k)
    #      = Sum p(o_k|x_k)*p(x_k|x_k-1)*p(x_k-1, o_1:k-1)
    #      = Sum p(o_k|x_k) * p(x_k|x_k-1) * a[k-1][x_k-1]
    (1...observations.length).each do |k|
      (0...num_states).each do |state|
        a[k][state] = emission[state][observations[k]] *
                      a[k-1].map.with_index { |a, i| a * transition[i][state] }.inject(:+)
      end
    end

    a
  end

  def num_states
    initial_probs.length
  end
end

require 'pry'

transition_rows = [[0.99, 0.01],
                   [0.1, 0.9]]

p = 1/6.to_f
emission_rows = [[p, p, p, p, p, p],
                 [p/5, p/5, p/5, p/5, p/5, 5*p]]
init = [0.5, 0.5]
hmm = HMM.new(transition_rows, emission_rows, init)
binding.pry
