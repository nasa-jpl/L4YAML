"""Pytest configuration for Python FFI tests.

Adds the l4yaml Python package to sys.path and handles
ROS 2 launch_testing plugin conflicts.
"""
import sys
from pathlib import Path

# Make l4yaml importable from the project's python/ directory
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
_PYTHON_PKG = _PROJECT_ROOT / "python"
if str(_PYTHON_PKG) not in sys.path:
    sys.path.insert(0, str(_PYTHON_PKG))


def pytest_configure(config):
    """Unregister ROS 2 plugins that conflict with standalone pytest."""
    pm = config.pluginmanager
    for name in ("launch_testing_ros_pytest_entrypoint", "launch_testing"):
        if pm.has_plugin(name):
            pm.unregister(name=name)
        plugin = pm.get_plugin(name)
        if plugin is not None:
            pm.unregister(plugin=plugin, name=name)
