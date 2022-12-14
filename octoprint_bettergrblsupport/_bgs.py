#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Written by:  Shell M. Shrader (https://github.com/synman/Octoprint-Bettergrblsupport)
# Copyright [2021] [Shell M. Shrader]
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# References
#
# https://web.archive.org/web/20211123161339/https://wiki.shapeoko.com/index.php/G-Code
# https://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=B69BCE8C0F7F5071B56B464AB4CA8C56?doi=10.1.1.15.7813&rep=rep1&type=pdf
# https://github.com/gnea/grbl/blob/master/doc/markdown/commands.md
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Jogging
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Configuration#10---status-report-mask
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Interface#grbl-push-messages
# https://reprap.org/wiki/G-codeimport os
#
import os
import time
import math

import re
# import requests
import threading

from timeit import default_timer as timer
from octoprint.events import Events

from .zprobe import ZProbe
from .xyprobe import XyProbe

zProbe = None
xyProbe = None

def load_grbl_descriptions(_plugin):
    path = os.path.dirname(os.path.realpath(__file__)) + os.path.sep + "static" + os.path.sep + "txt" + os.path.sep

    f = open(path + "grbl_errors.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblErrors[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching error id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])

    f = open(path + "grbl_alarms.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblAlarms[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching alarm id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])

    f = open(path + "grbl_settings.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblSettingsNames[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching setting id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])


def load_grbl_settings(_plugin):
    _plugin._logger.debug("_bgs: load_grbl_settings")

    _plugin.grblSettingsText = _plugin._settings.get(["grblSettingsText"])

    if not _plugin.grblSettingsText is None:
        for setting in _plugin.grblSettingsText.split("||"):
            if len(setting.strip()) > 0:

                _plugin._logger.debug("load_grbl_settings=[{}]".format(setting))

                set = setting.split("|")
                if not set is None:
                    _plugin.grblSettings.update({int(set[0]): [set[1], _plugin.grblSettingsNames.get(int(set[0]))]})
    return


def save_grbl_settings(_plugin):
    _plugin._logger.debug("_bgs: save_grbl_settings")

    ret = ""
    for id, data in sorted(_plugin.grblSettings.items(), key=lambda x: int(x[0])):
        ret = ret + "{}|{}|{}||".format(id, data[0], data[1])

    _plugin._logger.debug("save_grbl_settings=[{}]".format(ret))

    _plugin.grblSettingsText = ret

    return ret


def cleanup_due_to_uninstall(_plugin, remove_profile=True):
    _plugin._logger.debug("_bgs: cleanup_due_to_uninstall remove_profile=[{}]".format(remove_profile))

    # re-enable model size detection, sd card support
    _plugin._settings.global_set_boolean(["feature", "modelSizeDetection"], True)
    _plugin._settings.global_set_boolean(["feature", "sdSupport"], True)

    # load maps of disabled plugins & tabs
    disabledPlugins = _plugin._settings.global_get(["plugins", "_disabled"])
    disabledTabs = _plugin._settings.global_get(["appearance", "components", "disabled", "tab"])
    orderedTabs = _plugin._settings.global_get(["appearance", "components", "order", "tab"])
    orderedSidebar = _plugin._settings.global_get(["appearance", "components", "order", "sidebar"])

    if disabledPlugins == None:
        disabledPlugins = []

    if disabledTabs == None:
        disabledTabs = []

    if orderedTabs == None:
        orderedTabs = []

    if orderedSidebar == None:
        orderedSidebar = []

    # re-enable the printer safety check plugin
    if "printer_safety_check" in disabledPlugins:
        disabledPlugins.remove("printer_safety_check")

    # re-enable the gcodeviewer plugin
    if "gcodeviewer" in disabledPlugins:
        disabledPlugins.remove("gcodeviewer")
    if "plugin_gcodeviewer" in disabledTabs:
        disabledTabs.remove("plugin_gcodeviewer")

    # re-enable the built-in temp tab if it was hidden
    if "temperature" in disabledTabs:
        disabledTabs.remove("temperature")

    # re-enable the built-in control tab if it was hidden
    if "control" in disabledTabs:
        disabledTabs.remove("control")

    # remove me from ordered tabs if i'm in there
    if "plugin_bettergrblsupport" in orderedTabs:
        orderedTabs.remove("plugin_bettergrblsupport")

    # remove me from ordered sidebar if i'm in there
    if "plugin_bettergrblsupport" in orderedSidebar:
        orderedSidebar.remove("plugin_bettergrblsupport")

    if remove_profile:
        # restore the original printer profile (if it exists) and delete mine
        old_profile = _plugin._settings.get(["old_profile"])

        if not old_profile or not _plugin._printer_profile_manager.exists(old_profile):
            old_profile = "_default"

        _plugin._printer_profile_manager.select(old_profile)
        _plugin._printer_profile_manager.set_default(old_profile)

        if _plugin._printer_profile_manager.exists("_bgs"):
            _plugin._printer_profile_manager.remove("_bgs")
            _plugin._logger.debug("bgs profile has been deleted")

    _plugin._settings.global_set(["plugins", "_disabled"], disabledPlugins)
    _plugin._settings.global_set(["appearance", "components", "disabled", "tab"], disabledTabs)
    _plugin._settings.global_set(["appearance", "components", "order", "tab"], orderedTabs)
    _plugin._settings.global_set(["appearance", "components", "order", "sidebar"], orderedSidebar)

    # add pretty much all of grbl to long running commands list
    longCmds = _plugin._settings.global_get(["serial", "longRunningCommands"])
    if longCmds == None: longCmds = []

    if "$H" in longCmds: longCmds.remove("$H")
    if "G92" in longCmds: longCmds.remove("G92")
    if "G30" in longCmds: longCmds.remove("G30")
    if "G53" in longCmds: longCmds.append("G53")
    if "G54" in longCmds: longCmds.remove("G54")

    if "G20" in longCmds: longCmds.remove("G20")
    if "G21" in longCmds: longCmds.remove("G21")

    if "G90" in longCmds: longCmds.remove("G90")
    if "G91" in longCmds: longCmds.remove("G91")

    if "G38.1" in longCmds: longCmds.remove("G38.1")
    if "G38.2" in longCmds: longCmds.remove("G38.2")
    if "G38.3" in longCmds: longCmds.remove("G38.3")
    if "G38.4" in longCmds: longCmds.remove("G38.4")
    if "G38.5" in longCmds: longCmds.remove("G38.5")

    if "G0" in longCmds: longCmds.remove("G0")
    if "G1" in longCmds: longCmds.remove("G1")
    if "G2" in longCmds: longCmds.remove("G2")
    if "G3" in longCmds: longCmds.remove("G3")
    if "G4" in longCmds: longCmds.remove("G4")

    if "M3" in longCmds: longCmds.remove("M3")
    if "M4" in longCmds: longCmds.remove("M4")
    if "M5" in longCmds: longCmds.remove("M5")
    if "M7" in longCmds: longCmds.remove("M7")
    if "M8" in longCmds: longCmds.remove("M8")
    if "M9" in longCmds: longCmds.remove("M9")
    if "M30" in longCmds: longCmds.remove("M30")

    _plugin._settings.global_set(["serial", "longRunningCommands"], longCmds)
    _plugin._settings.global_set(["serial", "maxCommunicationTimeouts", "long"], 5)
    _plugin._settings.global_set_boolean(["serial", "neverSendChecksum"], False)
    _plugin._settings.global_set(["serial", "encoding"], "ascii")
    _plugin._settings.global_set(["terminalFilters"], _plugin.octo_filters)
    
    _plugin._settings.save()

# #-- EventHandlerPlugin mix-in
def on_event(_plugin, event, payload):
    subscribed_events = (Events.FILE_SELECTED, Events.FILE_ADDED, Events.PRINT_STARTED, Events.PRINT_CANCELLED, Events.PRINT_CANCELLING,
                        Events.PRINT_PAUSED, Events.PRINT_RESUMED, Events.PRINT_DONE, Events.PRINT_FAILED,
                        Events.PLUGIN_PLUGINMANAGER_UNINSTALL_PLUGIN, Events.PLUGIN_PLUGINMANAGER_DISABLE_PLUGIN, Events.UPLOAD,
                        Events.CONNECTING, Events.CONNECTED, Events.DISCONNECTING, Events.DISCONNECTED, Events.STARTUP, Events.SHUTDOWN)

    if event not in subscribed_events and payload is not None and payload.get("state_id") not in ("PAUSING", "STARTING"):
        _plugin._logger.debug('event [{}] received but not subscribed - discarding'.format(event))
        return

    _plugin._logger.debug("_bgs: on_event event=[{}] payload=[{}]".format(event, payload))

    # our plugin is being uninstalled
    if event in (Events.PLUGIN_PLUGINMANAGER_UNINSTALL_PLUGIN, Events.PLUGIN_PLUGINMANAGER_DISABLE_PLUGIN) and payload["id"] == _plugin._identifier:
        _plugin._logger.debug('we are being uninstalled/disabled :(')
        cleanup_due_to_uninstall(_plugin)
        _plugin._logger.debug('plugin cleanup completed (this house is clean)')
        return

    if _plugin._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
        return

    # - CONNECTING
    if event == Events.CONNECTING:
        _plugin.connectionState = event
        # let's make sure we don't have any commands queued up
        _plugin.grblCmdQueue.clear()

    # - CONNECTED
    if event == Events.CONNECTED:
        _plugin._logger.debug('machine connected')

        _plugin.connectionState = event
        _plugin.whenConnected = time.time()
        _plugin.autoSleepTimer = time.time()

        _plugin.is_operational = True
        _plugin._settings.set_boolean(["is_operational"], _plugin.is_operational)

        _plugin._printer.commands(["$I", "$G"])
        # _plugin._printer.fake_ack()

    # Disconnecting & Disconnected
    if event in (Events.DISCONNECTING, Events.DISCONNECTED):
        _plugin.connectionState = event
        _plugin.handshakeSent = False
        _plugin.grblState = "N/A"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="N/A"))

        _plugin.is_operational = False
        _plugin._settings.set_boolean(["is_operational"], _plugin.is_operational)

    # Print Starting
    if payload is not None and payload.get("state_id") == "STARTING":
        add_to_notify_queue(_plugin, ["Pgm Begin"])
        # threading.Thread(target=send_command_now, args=(_plugin._printer, _plugin._logger, "?")).start()
        _plugin._printer.commands("?", force=True)
        return

    # 'PrintStarted'
    if event == Events.PRINT_STARTED:
        if "HOLD" in _plugin.grblState.upper():
            _plugin._printer.commands(["~"], force=True)
        elif not _plugin.grblState.upper() in ("IDLE", "CHECK"):
            # we have to stop This
            _plugin._printer.cancel_print()
            return

        # reset our rate overrides
        _plugin.feedRate = 0
        _plugin.plungeRate = 0
        _plugin.powerRate = 0

        _plugin.grblState = "Run"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Run"))

        _plugin.is_printing = True
        _plugin._settings.set_boolean(["is_printing"], _plugin.is_printing)

        if _plugin.autoCooldown:
            activate_auto_cooldown(_plugin)

        return

    # Print ended (finished / failed / cancelled)
    if event in (Events.PRINT_CANCELLED, Events.PRINT_DONE, Events.PRINT_FAILED):
        _plugin.grblState = "Idle"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Idle"))

        _plugin.is_printing = False
        _plugin._settings.set_boolean(["is_printing"], _plugin.is_printing)

        return

    # Print Cancelling
    if event == Events.PRINT_CANCELLING:
        _plugin._logger.debug("cancelling job")

        if "HOLD" in _plugin.grblState.upper():
            _plugin._printer.commands(["~", "M5"], force=True)
        else:
            _plugin._printer.commands(["M5"], force=True)

    # Print Pausing
    if payload is not None and payload.get("state_id") == "PAUSING":
        _plugin._logger.debug("pausing job")

        _plugin.pausedPower = _plugin.grblPowerLevel
        _plugin.pausedPositioning = _plugin.positioning

        # _plugin._printer.fake_ack()

        # retract Z 5 if not laser mode
        if not is_laser_mode(_plugin):
            _plugin._printer.commands(["G91 G0 Z5"], force=True)

        _plugin._printer.commands(["M5", "?"], force=True)

    # Print Paused
    if event == Events.PRINT_PAUSED:
        _plugin._logger.debug("paused job")
        _plugin._printer.commands(["M5", "?", "!", "?"], force=True)

    # Print Resumed
    if event == Events.PRINT_RESUMED:
        _plugin._logger.debug("resuming job")
        _plugin._printer.commands(["~", "M3"], force=True)

        # move our spindle back down 5
        if not is_laser_mode(_plugin):
            _plugin._printer.commands(["G4 P10", "G91 G0 Z-5"], force=True)

        # make sure we are using whatever positioning mode was active before we paused
        _plugin._printer.commands(["G91" if _plugin.pausedPositioning == 1 else "G90"], force=True)

        _plugin.grblState = "Run"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Run"))

    # starting up
    if event == Events.STARTUP:
        _plugin._logger.info("starting up")

    # shutting down
    if event == Events.SHUTDOWN:
        _plugin._logger.info("shutting down")
        _plugin._settings.save()

    # File uploaded
    if event == Events.UPLOAD:
        if payload["path"].endswith(".gc") or payload["path"].endswith(".nc"):
            renamed_file = payload["path"][:len(payload["path"]) - 2] + "gcode"

            _plugin._logger.debug("renaming [%s] to [%s]", payload["path"], renamed_file)

            _plugin._file_manager.remove_file(payload["target"], renamed_file)
            _plugin._file_manager.move_file(payload["target"], payload["path"], renamed_file)

            generate_metadata_for_file(_plugin, renamed_file, notify=False, force=True)

    # 'FileAdded'
    if event == Events.FILE_ADDED:
        generate_metadata_for_file(_plugin, payload["path"], notify=False, force=True)

    # 'FileSelected'
    if event == Events.FILE_SELECTED:
        generate_metadata_for_file(_plugin, payload["path"], notify=True)
        return

    if event == Events.FILE_DESELECTED:
        return

    return


def do_framing(_plugin, data):
    _plugin._logger.debug("_bgs: do_framing data=[{}]".format(data))

    origin = data.get("origin").strip()
    length = float(data.get("length")) * _plugin.invertY
    width = float(data.get("width")) * _plugin.invertX

    send_frame_init_gcode(_plugin)

    if (origin == "grblTopLeft"):
        send_bounding_box_upper_left(_plugin, length, width)

    if (origin == "grblTopCenter"):
        send_bounding_box_upper_center(_plugin, length, width)

    if (origin == "grblTopRight"):
        send_bounding_box_upper_right(_plugin, length, width)

    if (origin == "grblCenterLeft"):
        send_bounding_box_center_left(_plugin, length, width)

    if (origin == "grblCenter"):
        send_bounding_box_center(_plugin, length, width)

    if (origin == "grblCenterRight"):
        send_bounding_box_center_right(_plugin, length, width)

    if (origin == "grblBottomLeft"):
        send_bounding_box_lower_left(_plugin, length, width)

    if (origin == "grblBottomCenter"):
        send_bounding_box_lower_center(_plugin, length, width)

    if (origin == "grblBottomRight"):
        send_bounding_box_lower_right(_plugin, length, width)

    send_frame_end_gcode(_plugin)


def send_frame_init_gcode(_plugin):
    _plugin._logger.debug("_bgs: send_frame_init_gcode")

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    # cancel jog if grbl 1.1+is_grbl_one_dot_one
    if is_grbl_one_dot_one(_plugin) and is_latin_encoding_available(_plugin):
        _plugin._printer.commands("CANCELJOG", force=True)

    # Linear mode, feedrate f% of max
    _plugin._printer.commands("G1 F{}".format(f))

    # turn on laser in weak mode if laser mode enabled
    if is_laser_mode(_plugin):
        _plugin._printer.commands("M3 S{}".format(_plugin.weakLaserValue))

    _plugin.grblState = "Jog"
    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Jog"))


def send_frame_end_gcode(_plugin):
    _plugin._logger.debug("_bgs: send_frame_end_gcode")

    queue_cmds_and_send(_plugin, ["?", "?", "?"])
    queue_cmds_and_send(_plugin, ["M5 S0 G0"])


def send_bounding_box_upper_left(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_upper_left y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ",x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))


def send_bounding_box_upper_center(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_upper_center y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2, f))


def send_bounding_box_upper_right(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_upper_right y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))


def send_bounding_box_center_left(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_center_left y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y / 2, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y / 2, f))


def send_bounding_box_center(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_center y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2 * -1, y / 2, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2, y / 2 * -1, f))


def send_bounding_box_center_right(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_center_right y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y / 2 * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y / 2 * -1, f))


def send_bounding_box_lower_left(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_lower_left y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))


def send_bounding_box_lower_center(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_lower_center y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2 * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x / 2 * -1, f))


def send_bounding_box_lower_right(_plugin, y, x):
    _plugin._logger.debug("_bgs: send_bounding_box_lower_right y=[{}] x=[{}]".format(y, x))

    f = int(float(_plugin.grblSettings.get(110)[0]) * (float(_plugin.framingPercentOfMaxSpeed) * .01))

    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x * -1, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y, f))
    _plugin._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", x, f))
    _plugin._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G1 ", y * -1, f))


def toggle_weak(_plugin):
    _plugin._logger.debug("_bgs: toggle_weak")

    # only execute if laser mode enabled
    if not is_laser_mode(_plugin):
        return

    f = int(float(_plugin.grblSettings.get(110)[0]))

    if _plugin.grblPowerLevel == 0:
        # turn on laser in weak mode
        _plugin._printer.commands("G1 F{} M3 S{:.2f}".format(f, _plugin.weakLaserValue))
        add_to_notify_queue(_plugin, ["Weak laser enabled"])
        res = "Laser Off"
    else:
        _plugin._printer.commands(["M3 S0", "M5", "G0"])
        add_to_notify_queue(_plugin, ["Weak laser disabled"])
        res = "Weak Laser"

    return res


def do_xyz_probe(_plugin, sessionId):
    # we need something in the background to track this
    threading.Thread(target=defer_do_xyz_probe, args=(_plugin, sessionId)).start()

def defer_do_xyz_probe(_plugin, sessionId):
    global zProbe
    global xyProbe

    do_simple_zprobe(_plugin, sessionId)

    # wait for the z probe to run out of scope
    while zProbe != None:
        time.sleep(1)

    do_xy_probe(_plugin, "XY", sessionId)


def do_xy_probe(_plugin, axes, sessionId):
    global xyProbe
    _plugin._logger.debug("_bgs: do_xy_probe step=[{}] axes=[{}] sessionId=[{}]".format(xyProbe._step if xyProbe != None else "N/A", axes, sessionId))

    frameOrigin = _plugin._settings.get(["frame_origin"])

    # do we do not support xy probe for center origins
    if "Center" in frameOrigin:
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                         sessionId=sessionId,
                                                                             title="X/Y Probe",
                                                                              text="You must select a <i>Material Framing</i> corner <b>Starting Position</b> to perform an X and/or Y axis probe.",
                                                                              hide=False,
                                                                             delay=0,
                                                                       notify_type="notice"))
        return

    if xyProbe == None:
        xyProbe = XyProbe(_plugin, xy_probe_hook, axes, sessionId)
        if axes == "Y": xyProbe._step = 0

    xyProbeTravel = float(_plugin._settings.get(["xyProbeTravel"]))
    xyf = float(_plugin.grblSettings.get(110 + xyProbe._step + 1)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)
    zf = float(_plugin.grblSettings.get(112)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)

    originInvert = -1 if "Left" in frameOrigin else 1
    distance = xyProbeTravel * _plugin.invertX * originInvert

    gcode = [
                "G21",
                "G0 G91 X{} F{}".format(distance, xyf),
                "G0 G91 Z{} F{}".format(15 * _plugin.invertZ * -1, zf),
                "G38.2 X{} F200".format(distance * -1)
            ]
    axis = "X"

    if xyProbe._step == 0 and axes != "X":
        originInvert = -1 if "Bottom" in frameOrigin else 1
        distance = xyProbeTravel * _plugin.invertY * originInvert

        gcode = [
                    "G21",
                    "G0 G91 Y{} F{}".format(distance, xyf),
                    "G0 G91 Z{} F{}".format(15 * _plugin.invertZ * -1, zf),
                    "G38.2 Y{} F200".format(distance * -1)
                ]
        axis = "Y"

    elif len(xyProbe._results) > 1 or (len(xyProbe._results) > 0 and axis in ("X", "Y")):
        if axes == "XY":
            text = "X/Y Axis Home has been calculated and set to machine position: X[<B>{:.3f}</B>] Y[<B>{:.3f}</B>]".format(xyProbe._results[0], xyProbe._results[1])
            xyf = float(_plugin.grblSettings.get(110)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)
            _plugin._printer.commands(["G0 G90 X0 Y0 F{}".format(xyf), "G91"])
        else:
            text = "{} Axis Home has been calculated and set to machine position: [<B>{:.3f}</B>]]".format(axes, xyProbe._results[0])
            _plugin._printer.commands(["G0 G90 {}0 F{}".format(axes, xyf), "G91"])

        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                         sessionId=xyProbe._sessionId,
                                                                             title="X/Y Probe",
                                                                              text=text,
                                                                              hide=False,
                                                                             delay=0,
                                                                       notify_type="info"))

        add_to_notify_queue(_plugin, [text.replace("<B>", "").replace("</B>", "")])

        xyProbe.teardown()
        xyProbe = None
        return
    elif xyProbe._step != -1:
        xyProbe.teardown()
        xyProbe = None
        return

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="xy_probe",
                                                                     sessionId=xyProbe._sessionId,
                                                                          axis=axis,
                                                                          axes=axes,
                                                                          step=xyProbe._step,
                                                                         gcode=gcode))

def xy_probe_hook(_plugin, result, position, axis):
    global xyProbe
    _plugin._logger.debug("_bgs: xy_probe_hook result=[{}] position=[{}] axis=[{}] sessionId=[{}]".format(result, position, axis, xyProbe._sessionId))

    # did we have a problem?
    if result == 0:
        xyProbe.teardown()
        xyProbe = None
        return

    notification = "X/Y Probe: [{}] axis result [{:.3f}]".format(axis, position)
    add_to_notify_queue(_plugin, [notification])

    # defer commands and setup of the next step
    threading.Thread(target=defer_do_xy_probe, args=(_plugin, position, axis, xyProbe._sessionId)).start()

def defer_do_xy_probe(_plugin, position, axis, sessionId):
    global xyProbe
    _plugin._logger.debug("_bgs: defer_do_xy_probe sessionId=[{}]".format(sessionId))

    _plugin.grblCmdQueue.append("%%% eat me %%%")
    _plugin._printer.commands("?")
    wait_for_empty_cmd_queue(_plugin)
    if xyProbe == None: return

    xyf = float(_plugin.grblSettings.get(110 + xyProbe._step)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)
    zf = float(_plugin.grblSettings.get(112)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)

    frameOrigin = _plugin._settings.get(["frame_origin"])
    originInvert = -1 if "Left" in frameOrigin else 1
    invert = _plugin.invertX

    if axis == "Y":
        originInvert = -1 if "Bottom" in frameOrigin else 1
        invert = _plugin.invertY

    program = int(float(_plugin.grblCoordinateSystem.replace("G", "")))
    program = -53 + program

    # set home for our current axis and travel back to where we started
    _plugin._printer.commands([
            "G10 P{} L2 {}{:f}".format(program, axis, position),
            "G0 {}{} Z{} F{}".format(axis, 10 * originInvert * invert, 15 * _plugin.invertZ, zf),
            "G0 G90 {}{} F{}".format(axis, 10 * originInvert * invert * -1, xyf),
            "G91"
        ])

    do_xy_probe(_plugin, xyProbe._axes, sessionId)


def do_simple_zprobe(_plugin, sessionId):
    _plugin._logger.debug("_bgs: do_simple_zprobe sessionId=[{}]".format(sessionId))

    global zProbe

    if not zProbe == None:
        zProbe.teardown()
        zProbe = None

    zProbe = ZProbe(_plugin, simple_zprobe_hook, sessionId)

    zTravel = _plugin.zLimit if _plugin.zProbeTravel == 0 else _plugin.zProbeTravel
    zTravel = zTravel * -1 * _plugin.invertZ

    gcode = "G91 G21 G38.2 Z{} F100".format(zTravel)
    zProbe._locations = [{"gcode": gcode,  "action": "simple_zprobe", "location": "Current"}]

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_zprobe",
                                                                     sessionId=zProbe._sessionId,
                                                                         gcode=gcode))


def simple_zprobe_hook(_plugin, result, position):
    global zProbe
    _plugin._logger.debug("_bgs: simple_zprobe_hook result=[{}] position=[{}] sessionId=[{}]".format(result, position, zProbe._sessionId))

    sessionId = zProbe._sessionId

    type = ""
    title = ""
    text = ""
    notify_type = ""

    z0 = position + _plugin.zProbeOffset * _plugin.invertZ * -1

    if result == 1:
        # defer commands because we are out of sync
        threading.Thread(target=defer_simple_z_probe, args=(_plugin, z0)).start()

        type="simple_notify"
        title="Single Point Z-Probe"
        text = "Z Axis Home has been calculated and set to machine position: [<B>{:.3f}</B>]".format(z0)
        notify_type="info"

        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type=type,
                                                                         sessionId=sessionId,
                                                                             title=title,
                                                                              text=text,
                                                                              hide=False,
                                                                             delay=0,
                                                                       notify_type=notify_type))

        add_to_notify_queue(_plugin, [text.replace("<B>", "").replace("</B>", "")])

    _plugin._logger.debug("zprobe hook position: [%f] result: [%d]", position, result)

def defer_simple_z_probe(_plugin, z0):
    global zProbe

    _plugin.grblCmdQueue.append("%%% eat me %%%")
    _plugin._printer.commands("?")
    wait_for_empty_cmd_queue(_plugin)

    program = int(float(_plugin.grblCoordinateSystem.replace("G", "")))
    program = -53 + program

    _plugin._printer.commands(["G91", "G21", "G10 P{} L2 Z{:f}".format(program, z0), "G0 Z{}".format(_plugin.zProbeEndPos * _plugin.invertZ)])

    zProbe.teardown()
    zProbe = None


def do_multipoint_zprobe(_plugin, sessionId):
    global zProbe
    _plugin._logger.debug("_bgs: do_multipoint_zprobe step=[{}] sessionId=[{}]".format(zProbe._step + 1 if zProbe != None else 0, sessionId))

    if zProbe == None:
        zProbe = ZProbe(_plugin, multipoint_zprobe_hook, sessionId)

    zProbe._step+=1

    if zProbe._step == 0:
        origin = _plugin._settings.get(["frame_origin"])
        width = float(_plugin._settings.get(["frame_width"])) * _plugin.invertX
        length = float(_plugin._settings.get(["frame_length"])) * _plugin.invertY
        preamble = "$J=" if is_grbl_one_dot_one(_plugin) else "G1 "

        zTravel = _plugin.zLimit if _plugin.zProbeTravel == 0 else _plugin.zProbeTravel
        zTravel = zTravel * -1 * _plugin.invertZ

        feedrate = float(_plugin.grblSettings.get(110)[0]) * (_plugin.framingPercentOfMaxSpeed * .01)

        if origin == "grblTopLeft":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width, feedrate), "action": "move", "location": "Top Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Right"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length * -1, feedrate), "action": "move", "location": "Bottom Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Right"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width * -1, feedrate), "action": "move", "location": "Bottom Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Left"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Top Left"},
                                ]
        elif origin == "grblTopCenter":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2 * -1, feedrate), "action": "move", "location": "Center Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Right"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Center Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2, feedrate), "action": "move", "location": "Top Center"},
                                ]
        elif origin == "grblTopRight":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Right"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length * -1, feedrate), "action": "move", "location": "Bottom Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Right"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width * -1, feedrate), "action": "move", "location": "Bottom Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Left"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length, feedrate), "action": "move", "location": "Top Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Left"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2 * -1, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2, feedrate), "action": "move", "location": "Top Right"},
                                ]
        elif origin == "grblCenterLeft":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Left"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2, feedrate), "action": "move", "location": "Top Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2 * -1, feedrate), "action": "move", "location": "Center Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Right"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Center"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2 * -1, feedrate), "action": "move", "location": "Center Left"},
                                ]
        elif origin == "grblCenter":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Top Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2, feedrate), "action": "move", "location": "Top Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Center"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2, feedrate), "action": "move", "location": "Top Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Right"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2 * -1, feedrate), "action": "move", "location": "Center Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Right"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Right"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2 * -1, feedrate), "action": "move", "location": "Bottom Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Center"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2 * -1, feedrate), "action": "move", "location": "Bottom Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Left"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2, feedrate), "action": "move", "location": "Center Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2, feedrate), "action": "move", "location": "Center"},
                                ]
        elif origin == "grblCenterRight":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Right"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Center Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Left"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2, feedrate), "action": "move", "location": "Top Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Center"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2 * -1, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2, feedrate), "action": "move", "location": "Center Right"},
                                ]
        elif origin == "grblBottomLeft":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Left"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length, feedrate), "action": "move", "location": "Top Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width, feedrate), "action": "move", "location": "Top Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Right"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length * -1, feedrate), "action": "move", "location": "Bottom Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Right"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Left"},
                                ]
        elif origin == "grblBottomCenter":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2, feedrate), "action": "move", "location": "Center Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Left"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2, feedrate), "action": "move", "location": "Top Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2 * -1, feedrate), "action": "move", "location": "Center Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center Right"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width / 2 * -1, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Center"},
                                ]
        elif origin == "grblBottomRight":
            zProbe._locations = [
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Right"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width * -1, feedrate), "action": "move", "location": "Bottom Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Bottom Left"},
                                    {"gcode": "{}G91 G21 Y{:f} F{}".format(preamble, length, feedrate), "action": "move", "location": "Top Left"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Left"},
                                    {"gcode": "{}G91 G21 X{:f} F{}".format(preamble, width, feedrate), "action": "move", "location": "Top Right"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Top Right"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2 * -1, length / 2 * -1, feedrate), "action": "move", "location": "Center"},
                                    {"gcode": "G91 G21 G38.2 Z{} F100".format(zTravel),  "action": "probe", "location": "Center"},
                                    {"gcode": "{}G91 G21 X{:f} Y{:f} F{}".format(preamble, width / 2, length / 2 * -1, feedrate), "action": "move", "location": "Bottom Right"},
                                ]
        else:
            # we shouldn't be here
            zProbe.teardown()
            zProbe = None
            return
    else:
        if zProbe._step > len(zProbe._locations) - 1:
            positionTuple = zProbe.resultByCalc(_plugin._settings.get(["zprobeCalc"]))

            position = positionTuple[0]
            location = positionTuple[1]

            program = int(float(_plugin.grblCoordinateSystem.replace("G", "")))
            program = -53 + program

            queue_cmds_and_send(_plugin, ["G10 P{} L2 Z{:f}".format(program, position)])

            text = "Z Axis Home has been calculated and set to machine position: [<B>{:.3f}</B>] ({})\r\n\r\n Result Details:\r\n\r\nVariance: {:.3f}mm\r\n\r\nHighest Point: {:.3f} ({})\r\nLowest Point: {:.3f} ({})\r\nMean Point: {:.3f}\r\nComputed Average: {:.3f}".format(
                position,
                location,
                zProbe.resultByCalc("GAP")[0],
                zProbe.resultByCalc("MIN")[0], zProbe.resultByCalc("MIN")[1],
                zProbe.resultByCalc("MAX")[0], zProbe.resultByCalc("MAX")[1],
                zProbe.resultByCalc("MEAN")[0],
                zProbe.resultByCalc("AVG")[0]
            )
            _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                             sessionId=zProbe._sessionId,
                                                                                 title="Multipoint Z-Probe",
                                                                                  text=text,
                                                                                  hide=False,
                                                                                 delay=0,
                                                                           notify_type="info"))

            add_to_notify_queue(_plugin, [text.replace("<B>", "").replace("</B>", "")])

            zProbe.teardown()
            zProbe = None
            return

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="multipoint_zprobe",
                                                                     sessionId=zProbe._sessionId,
                                                                   instruction=zProbe.getCurrentLocation()))


def multipoint_zprobe_hook(_plugin, result, position):
    global zProbe
    _plugin._logger.debug("_bgs: multipoint_zprobe_hook result=[{}] position=[{}] sessionId=[{}]".format(result, position, zProbe._sessionId))

    # did we have a problem?
    if result == 0:
        zProbe.teardown()
        zProbe = None
        return
    else:
        location = zProbe.getCurrentLocation()['location']
        notification = "Z-Probe [{}] location result [{:.3f}]".format(location, position)
        add_to_notify_queue(_plugin, [notification])

        # max z feed rate -- we'll do 50% of it
        zf = round(float(_plugin.grblSettings.get(112)[0]) * .5)
        _plugin._printer.commands("{}G91 G21 Z{} F{}".format("$J=" if is_grbl_one_dot_one(_plugin) else "G0 ", _plugin.zProbeEndPos, zf))

    # defer setup of the next step
    threading.Thread(target=defer_do_multipoint_zprobe, args=(_plugin, zProbe._sessionId)).start()


def defer_do_multipoint_zprobe(_plugin, sessionId):
    global zProbe
    _plugin._logger.debug("_bgs: defer_do_multipoint_zprobe sessionId=[{}]".format(sessionId))

    _plugin.grblCmdQueue.append("%%% eat me %%%")
    _plugin._printer.commands("?")
    wait_for_empty_cmd_queue(_plugin)

    if zProbe != None:
        do_multipoint_zprobe(_plugin, sessionId)


def multipoint_zprobe_move(_plugin):
    global zProbe
    _plugin._logger.debug("_bgs: multipoint_zprobe_move sessionId=[{}]".format(zProbe._sessionId))

    # setup the next step
    do_multipoint_zprobe(_plugin, zProbe._sessionId)


def grbl_alarm_or_error_occurred(_plugin):
    global zProbe
    global xyProbe

    _plugin._logger.debug("_bgs: grbl_alarm_or_error_occurred")

    if zProbe != None:
        zProbe.teardown()
        zProbe = None

    if xyProbe != None:
        xyProbe.teardown()
        xyProbe = None


def activate_auto_cooldown(_plugin):
    _plugin._logger.debug("_bgs: activate_auto_cooldown")
    threading.Thread(target=auto_cooldown_monitor, args=(_plugin,)).start()


def auto_cooldown_monitor(_plugin):
    _plugin._logger.debug("_bgs: auto_cooldown_monitor")

    frequency = _plugin.autoCooldownFrequency * 60
    duration = _plugin.autoCooldownDuration * 60

    while _plugin._printer.is_printing():
        _plugin._logger.debug("auto cooldown loop started")

        startTime = time.time()

        while _plugin._printer.is_printing() and time.time() < startTime + frequency:
            time.sleep(1)

        if _plugin._printer.is_printing():
            _plugin._logger.debug("auto cooldown pausing job")
            _plugin._printer.pause_print()
        else:
            _plugin._logger.debug("job appears to have unexpectedly ended while waiting for cooldown frequency")
            break

        startTime = time.time()

        while (_plugin._printer.is_pausing() or _plugin._printer.is_paused()) and time.time() < startTime + duration:
            time.sleep(1)

        if _plugin._printer.is_paused():
            _plugin._logger.debug("auto cooldown resuming job")
            _plugin._printer.resume_print()
        else:
            _plugin._logger.debug("job appears to have unexpectedly ended while waiting for cooldown duration")
            continue

        _plugin._logger.debug("auto cooldown loop complete")
    _plugin._logger.debug("auto cooldown monitor shutting down")


def queue_cmds_and_send(_plugin, cmds, wait=False):
    _plugin._logger.debug("_bgs: queue_cmds_and_send cmds=[{}] wait=[{}]".format(cmds, wait))

    for cmd in cmds:
        _plugin._logger.debug("queuing command [%s] wait=%r", cmd, wait)
        _plugin.grblCmdQueue.append(cmd)

    if wait:
        wait_for_empty_cmd_queue(_plugin)


def wait_for_empty_cmd_queue(_plugin):
    _plugin._logger.debug("_bgs: wait_for_empty_cmd_queue")

    while len(_plugin.grblCmdQueue) > 0:
        time.sleep(.001)

    _plugin._logger.debug("done waiting for command queue to drain")


def add_to_notify_queue(_plugin, notifications):
    _plugin._logger.debug("_bgs: add_to_notify_queue notifications=[{}]".format(notifications))

    if not zProbe is None:
        zProbe.notify(notifications)
    if not xyProbe is None:
        xyProbe.notify(notifications)

    for notification in notifications:
        # limit notify queue depth to avoid spamming
        if len(_plugin.notifyQueue) >= 100:
            _plugin.notifyQueue.pop(0)
            _plugin._logger.debug("dropping oldest notification")

        _plugin._logger.debug("queuing notification [%s] - depth [%d]", notification, len(_plugin.notifyQueue) + 1)
        _plugin.notifyQueue.append(notification)


def generate_metadata_for_file(_plugin, filename, notify=False, force=False):
    metadata = _plugin._file_manager.get_metadata("local", filename)
    created = os.path.getctime(_plugin._file_manager.path_on_disk("local", filename))

    processing = True if metadata.get("bgs_processing") == "true" else False
    length = metadata.get("bgs_length")
    width = metadata.get("bgs_width")
    origin = metadata.get("bgs_origin")
    timestamp = metadata.get("bgs_timestamp")

    if timestamp is None or created > timestamp:
        force = True

    _plugin._logger.debug("_bgs: generate_metadata_for_file filename=[{}] notify=[{}] force=[{}] processing=[{}] length=[{}] width=[{}] origin=[{}]".format(filename, notify, force, processing, length, width, origin))

    if length is None or width is None or origin is None or force:
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_width")
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_length")
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_origin")

        if processing and notify:
            threading.Thread(target=wait_for_metadata_processing, args=(_plugin, filename, notify)).start()
        else:
            _plugin._file_manager.set_additional_metadata("local", filename, "bgs_processing", "true", overwrite=True)
            threading.Thread(target=defer_generate_metadata_for_file, args=(_plugin, filename, notify)).start()
    else:
        if notify:
            _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                                 length=length,
                                                                                  width=width,
                                                                                  origin=origin))

def defer_generate_metadata_for_file(_plugin, filename, notify):
    _plugin._logger.debug("_bgs: defer_generate_metadata_for_file filename=[{}] notify=[{}]".format(filename, notify))

    try:
        file = _plugin._file_manager.path_on_disk("local", filename)
        created = os.path.getctime(file)

        f = open(file, 'r')

        minX = float("inf")
        minY = float("inf")
        maxX = float("-inf")
        maxY = float("-inf")

        x = float(0)
        y = float(0)

        overX = False
        overY = False
        underX = False
        underY = False

        lastGCommand = ""
        positioning = _plugin.positioning
        origin = ""

        start = timer()

        for line in f:
            # skip comments / etc
            if line.upper().lstrip().startswith((";", "(", "%")): continue

            # save our G command for shorthand post processors
            if line.upper().lstrip().startswith("G"):
                lastGCommand = line.lstrip()[:3] if line.lstrip()[2:3].isnumeric() else line.lstrip()[:2]

            # use our saved G command if our line starts with a coordinate
            if line.upper().lstrip().startswith(("X", "Y", "Z")):
                command = lastGCommand.upper() + " " + line.upper().strip()
            else:
                command = line.upper().strip()

            # only G commands matter (except G53)
            if not command.upper().lstrip().startswith("G") or "G53" in command.upper():
                continue

            if "G90" in command.upper():
                # absolute positioning
                positioning = 0

            if "G91" in command.upper():
                # relative positioning
                positioning = 1

            # match = re.search(r"^G([0][0123]|[0123])(\D.*[Xx]|[Xx])\ *(-?[\d.]+).*", command)
            match = re.search(r".*[X]\ *(-?[\d.]+).*", command)
            # _plugin._logger.debug("command=[{}]".format(command))
            if not match is None:
                x = float(match.groups(1)[0]) if positioning == 0 else x + float(match.groups(1)[0])
                if x < minX:
                    if not underX and x < -1:
                        _plugin._logger.debug("underX x=[{}]".format(x))
                        underX = True
                    minX = x
                if x > maxX:
                    if not overX and x > 1:
                        _plugin._logger.debug("overX x=[{}]".format(x))
                        overX = True
                    maxX = x

            # match = re.search(r"^G([0][0123]|[0123])(\D.*[Yy]|[Yy])\ *(-?[\d.]+).*", command)
            match = re.search(r".*[Y]\ *(-?[\d.]+).*", command)
            if not match is None:
                y = float(match.groups(1)[0]) if positioning == 0 else y + float(match.groups(1)[0])
                if y < minY:
                    if not underY and y <= -1:
                        _plugin._logger.debug("underY y=[{}]".format(y))
                        underY = True
                    minY = y
                if y > maxY:
                    if not overY and y > 1:
                        _plugin._logger.debug("overY y=[{}]".format(y))
                        overY = True
                    maxY = y

        length = math.ceil(maxY - minY)
        width = math.ceil(maxX - minX)

        # bottom
        if overY and not underY and overX and not underX: origin = "grblBottomLeft"
        if overY and not underY and overX and underX: origin = "grblBottomCenter"
        if overY and not underY and not overX and underX: origin = "grblBottomRight"

        # center
        if overY and underY and overX and not underX: origin = "grblCenterLeft"
        if overY and underY and overX and underX: origin = "grblCenter"
        if overY and underY and not overX and underX: origin = "grblCenterRight"

        # top
        if not overY and underY and overX and not underX: origin = "grblTopLeft"
        if not overY and underY and overX and underX: origin = "grblTopCenter"
        if not overY and underY and not overX and underX: origin = "grblTopRight"

        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_length", length, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_width", width, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_origin", origin, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_timestamp", created, overwrite=True)

        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_processing")

        _plugin._logger.debug('finished reading file=[{}] length=[{}] width=[{}] origin=[{}] positioning=[{}] time=[{}]'.format(filename, length, width, origin, positioning, timer() - start))

        if notify:
            _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                             length=length,
                                                                             width=width,
                                                                             origin=origin))
    except BaseException as e:
        _plugin._logger.error("defer_generate_metadata_for_file: [{}]".format(str(e)))


def wait_for_metadata_processing(_plugin, filename, notify):
    _plugin._logger.debug("_bgs: wait_for_metadata_processing filename=[{}] notify=[{}]".format(filename, notify))

    metadata = _plugin._file_manager.get_metadata("local", filename)
    processing = True if metadata.get("bgs_processing") == "true" else False
    seconds = 0

    while seconds < 300 and processing:
        time.sleep(1)
        metadata = _plugin._file_manager.get_metadata("local", filename)
        processing = True if metadata.get("bgs_processing") == "true" else False
        seconds += 1

    if not processing and notify:
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                            length=metadata.get("bgs_length"),
                                                                             width=metadata.get("bgs_width"),
                                                                             origin=metadata.get("bgs_origin")))
    else:
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_processing")
        _plugin._logger.warning("gave up waiting for metadata processing")


def is_laser_mode(_plugin):
    _plugin._logger.debug("_bgs: is_laser_mode={}".format(int(float(_plugin.grblSettings.get(32)[0])) != 0))
    return int(float(_plugin.grblSettings.get(32)[0])) != 0


def is_grbl_one_dot_one(_plugin):
    oneDotOne = "VER:1." in _plugin.grblVersion and "VER:1.0" not in _plugin.grblVersion
    _plugin._logger.debug("_bgs: is_grbl_one_dot_one result=[{}]".format(oneDotOne))
    return oneDotOne

def is_grbl_esp32(_plugin):
    oneDotOne = "VER:1." in _plugin.grblVersion and "VER:1.0" not in _plugin.grblVersion and "VER:1.1" not in _plugin.grblVersion
    _plugin._logger.debug("_bgs: is_grbl_esp32 result=[{}]".format(oneDotOne))
    return oneDotOne

def is_grbl_fluidnc(_plugin):
    oneDotOne = " FLUIDNC " in _plugin.grblVersion.upper()
    _plugin._logger.debug("_bgs: is_grbl_fluidnc result=[{}]".format(oneDotOne))
    return oneDotOne


def is_latin_encoding_available(_plugin):
    octoprintVersion = _plugin.octoprintVersion
    latinEncoding = int(octoprintVersion.split(".")[0]) > 1 or int(octoprintVersion.split(".")[1]) >= 8
    _plugin._logger.debug("_bgs: is_latin_encoding_available result=[{}]".format(latinEncoding))
    return latinEncoding


def do_fake_ack(printer, logger):
    time.sleep(1)
    printer.fake_ack()
    logger.debug("_bgs: do_fake_ack")


def send_command_now(printer, logger, cmd):
    try:
        printer.commands(cmd, force=True)
        logger.debug("_bgs: send_command")
    except Exception as e:
        logger.error("_bgs: send_command_now: %s" % e)
