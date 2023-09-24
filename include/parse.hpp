#pragma once

#include <cstdint>
#include <iostream>
#include <vector>

namespace apr {
struct Dependency {
  std::int32_t from;
  std::int32_t to;
};

struct Input {
  std::vector<std::int32_t> required;   // n - number of groups
  std::vector<std::int32_t> stages;     // m - number of switches
  std::vector<std::int32_t> capacity;   // m
  std::vector<Dependency> dependencies; // d - number of dependencies
};

auto Parse(std::istream &input) -> Input {
  std::int32_t n = 0;
  input >> n;
  if (n <= 1) {
    throw std::invalid_argument(
        "Number of groups of rules must be greater than 1");
  }

  std::int32_t m = 0;
  input >> m;
  if (m < 1) {
    throw std::invalid_argument("Number of switches must be positive");
  }

  Input in;

  in.required.resize(n);
  for (auto &req : in.required) {
    input >> req;
  }

  in.stages.resize(m);
  for (auto &st : in.stages) {
    input >> st;
  }

  in.capacity.resize(m);
  for (auto &c : in.capacity) {
    input >> c;
  }

  std::int32_t d = 0;
  input >> d;
  if (d < 0) {
    throw std::invalid_argument("Number of groups of rules must be positive");
  }

  in.dependencies.resize(d);
  for (auto &dep : in.dependencies) {
    input >> dep.from >> dep.to;
  }

  return in;
}
} // namespace apr